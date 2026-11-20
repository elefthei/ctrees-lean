/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Segments
public import Logic.Utils.Execution

/-!
# Abstract turn models and pool simulation

The bridge between an abstract stepping model (a partial transition on an opaque state, emitting a
finite observation list per turn) and the concrete scheduled interpretation of a thread pool. Every
scheduling decision is visible: a silent selection step under nondeterministic scheduling, a logged
`.inr slot` under round robin, where program observations are relabelled under `.inl`
(← `CTree/Interp/Yield/Execution.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction
open ITree (Effect)

/-! ## Turn-structured emission

A finite list of turns, each one selection step followed by its logs. -/

section EmitTurns
variable {B : Effect.{u}} {W I X Y : Type u}

/-- Each turn is one visible step followed by its logs. -/
def emit_turns (turns : List (List W)) (t : ctreeW W B X) : ctreeW W B X :=
  match turns with
  | [] => t
  | ev :: rest => .step (emit_list ev (emit_turns rest t))

theorem emit_turns_app (xs ys : List (List W)) (t : ctreeW W B X) :
    emit_turns (xs ++ ys) t = emit_turns xs (emit_turns ys t) := by
  induction xs with
  | nil => rfl
  | cons ev xs ih => simp [emit_turns, ih]

theorem emit_turns_equ (turns : List (List W)) {t u : ctreeW W B X} (h : t = u) :
    emit_turns turns t = emit_turns turns u :=
  h ▸ rfl

theorem emit_turns_chain {R : Rel (ctreeW W B X) (ctreeW W B X)} (hR : Chain (sb Eq) R)
    (turns : List (List W)) {t u : ctreeW W B X} (h : R t u) :
    R (emit_turns turns t) (emit_turns turns u) := by
  induction turns with
  | nil => exact h
  | cons ev rest ih => exact b_chain hR _ _ (step_sb_step_gen rfl (emit_list_chain hR ev ih))

theorem emit_turns_sbisim (turns : List (List W)) {t u : ctreeW W B X} (h : t ~ u) :
    emit_turns turns t ~ emit_turns turns u :=
  emit_turns_chain (gfp_chain _) turns h

theorem emit_turns_bind (turns : List (List W)) (t : ctreeW W B X) (k : X → ctreeW W B Y) :
    (emit_turns turns t >>= k) = emit_turns turns (t >>= k) := by
  induction turns with
  | nil => rfl
  | cons ev rest ih => simp [emit_turns, emit_list_bind, ih]

theorem emit_turns_ret_bind (turns : List (List W)) (x : X) (k : X → ctreeW W B Y) :
    (emit_turns turns (pure x) >>= k) = emit_turns turns (k x) := by
  rw [emit_turns_bind, pure_bind']

/-- Finitely many leading guards are invisible. -/
theorem rr_guards_sbisim (k : Nat) (t : ctreeW W B X) : rr_guards k t ~ t := guards_sbisim k t

theorem sb_chain_guards_l {R : Rel (ctreeW W B X) (ctreeW W B X)} (hR : Chain (sb Eq) R)
    (k : Nat) (t u : ctreeW W B X) (h : R t u) : R (rr_guards k t) u :=
  sbisim_clos_sb hR _ t u u (rr_guards_sbisim k t) h (sbisim_refl u)

theorem sb_chain_guards_r {R : Rel (ctreeW W B X) (ctreeW W B X)} (hR : Chain (sb Eq) R)
    (k : Nat) (t u : ctreeW W B X) (h : R t u) : R t (rr_guards k u) :=
  sbisim_clos_sb hR t t u _ (sbisim_refl t) h (sbisim_symm (rr_guards_sbisim k u))

/-- Repeating turn batches: the turn-structured twin of `emit_batches`. -/
def emit_turn_batches (batch : I → List (List W)) (next : I → I) (i : I) : ctreeW W B X :=
  CTree.iter (fun j => emit_turns (batch j) (pure (Sum.inl (next j)))) i

theorem emit_turn_batches_unfold (batch : I → List (List W)) (next : I → I) (i : I) :
    (emit_turn_batches batch next i : ctreeW W B X) =
      emit_turns (batch i) (.guard (emit_turn_batches batch next (next i))) := by
  rw [emit_turn_batches, unfold_iter, emit_turns_ret_bind]
  rfl

theorem emit_turn_batches_unfold_sbisim (batch : I → List (List W)) (next : I → I) (i : I) :
    (emit_turn_batches batch next i : ctreeW W B X) ~
      emit_turns (batch i) (emit_turn_batches batch next (next i) : ctreeW W B X) := by
  rw [emit_turn_batches_unfold]
  exact emit_turns_sbisim _ (sb_guard _)

/-- A root family that runs its own turn batch each round is the batch loop. A nonempty batch
always begins with a visible step, which makes the coinduction productive. -/
theorem emit_turn_batches_bisim (batch : I → List (List W)) (next : I → I) (Inv : I → Prop)
    (root : I → ctreeW W B X) (hnext : ∀ i, Inv i → Inv (next i))
    (hnonempty : ∀ i, Inv i → batch i ≠ [])
    (hroot : ∀ i, Inv i → root i ~ emit_turns (batch i) (root (next i))) :
    ∀ i, Inv i → root i ~ (emit_turn_batches batch next i : ctreeW W B X) := by
  intro i hi
  refine coinduction (b := sb Eq) (ι := {i // Inv i}) (fun i => root i.1)
    (fun i => emit_turn_batches batch next i.1) ?_ ⟨i, hi⟩
  rintro R hR cih ⟨i, hi⟩
  refine sbisim_clos_sb (.step hR) _ _
    (emit_turns (batch i) (emit_turn_batches batch next (next i)))
    _ (hroot i hi) ?_ (sbisim_symm (emit_turn_batches_unfold_sbisim batch next i))
  match hb : batch i, hnonempty i hi with
  | ev :: rest, _ =>
    exact step_sb_step_gen rfl
      (emit_list_chain hR ev (emit_turns_chain hR rest (cih ⟨next i, hnext i hi⟩)))

end EmitTurns

/-- Branch-by-branch bisimulation of two `brSn` nodes (Lean helper for the `brS (branchn _)`
steps of the Rocq proofs). -/
theorem step_sb_brSn_id {E B : Effect.{u}} [Bn -< B] {X : Type u}
    {R : Rel (CTree E B X) (CTree E B X)}
    {m : Nat} {k k' : Fin m → CTree E B X} (h : ∀ i, R (k i) (k' i)) :
    sb Eq R (CTree.brSn m k) (CTree.brSn m k') :=
  step_sb_br_id_gen _ _ _ fun _ => step_sb_step_gen rfl (h _)

/-! ## The two models -/

section ModelND
variable {St Act W X : Type} {B : Effect.{0}} [Bn -< B] (n : Nat) (actor : Fin (n + 1) → Act)
  (step : Act → St → Option (St × List W))

/-- Every nondeterministic turn begins with exactly one visible branch; the post-effect guards
are invisible, not additional choices. -/
def model_nd (s : St) : ctreeW W B X :=
  CTree.iter (fun state => CTree.brSn (n + 1) fun i =>
    match step (actor i) state with
    | none => .stuck
    | some (next, logs) => emit_list logs (pure (.inl next))) s

theorem unfold_model_nd (s : St) :
    (model_nd n actor step s : ctreeW W B X) =
      CTree.brSn (n + 1) fun i =>
        match step (actor i) s with
        | none => .stuck
        | some (next, logs) => emit_list logs (.guard (model_nd n actor step next)) := by
  rw [model_nd, unfold_iter]
  simp only [CTree.brSn, brS'_bind]
  congr 1; funext x
  split <;> simp [emit_list_ret_bind] <;> rfl

theorem unfold_model_nd_sbisim (s : St) :
    (model_nd n actor step s : ctreeW W B X) ~
      CTree.brSn (n + 1) fun i =>
        match step (actor i) s with
        | none => .stuck
        | some (next, logs) => emit_list logs (model_nd n actor step next : ctreeW W B X) := by
  rw [unfold_model_nd]
  refine b_chain (gfp_chain (sb Eq)) _ _ (step_sb_brSn_id fun i => ?_)
  split
  · exact sbisim_refl _
  · exact emit_list_sbisim _ (sb_guard _)

/-- Exactly one selection label followed by the returned observation list. -/
theorem model_turn_finite_steps [LawfulSubeffect Bn B] (i : Fin (n + 1)) (s next : St)
    (logs : List W) (h : step (actor i) s = some (next, logs)) :
    FiniteSteps (model_nd n actor step s : ctreeW W B X) (turn_labels logs)
      (.guard (model_nd n actor step next)) := by
  refine .cons (u := emit_list logs (.guard (model_nd n actor step next))) ?_
    (finite_steps_emit_list logs _)
  rw [unfold_model_nd]
  have := trans_brS' (B₁ := Bn) (B := B) (c := ⟨n + 1⟩) (fun x : ULift (Fin (n + 1)) =>
    match step (actor x.down) s with
    | none => (.stuck : ctreeW W B X)
    | some (next, logs) => emit_list logs (.guard (model_nd n actor step next))) ⟨i⟩
  simp only [h] at this
  exact this

end ModelND

section ModelRR
variable {St Act W X : Type} {B : Effect.{0}} (n : Nat) (actor : Fin (n + 1) → Act)
  (step : Act → St → Option (St × List W))

/-- Every turn logs its selected slot before the program's observation list. -/
def model_rr (s : St) (cursor : Nat) : ctreeW (W ⊕ Nat) B X :=
  CTree.iter (fun p : St × Nat =>
    .vis (E := writerE (W ⊕ Nat)) (.inr (slot_index (rr_pick n p.2))) fun _ =>
      match step (actor (rr_pick n p.2)) p.1 with
      | none => .stuck
      | some (next, logs) => emit_list (logs.map .inl) (pure (.inl (next, p.2 + 1)))) (s, cursor)

theorem unfold_model_rr (s : St) (cursor : Nat) :
    (model_rr n actor step s cursor : ctreeW (W ⊕ Nat) B X) =
      .vis (E := writerE (W ⊕ Nat)) (.inr (slot_index (rr_pick n cursor))) fun _ =>
        match step (actor (rr_pick n cursor)) s with
        | none => .stuck
        | some (next, logs) =>
          emit_list (logs.map .inl) (.guard (model_rr n actor step next (cursor + 1))) := by
  rw [model_rr, unfold_iter]
  simp only [vis_bind]
  congr 1; funext x
  split <;> simp [emit_list_ret_bind] <;> rfl

theorem unfold_model_rr_sbisim (s : St) (cursor : Nat) :
    (model_rr n actor step s cursor : ctreeW (W ⊕ Nat) B X) ~
      .vis (E := writerE (W ⊕ Nat)) (.inr (slot_index (rr_pick n cursor))) fun _ =>
        match step (actor (rr_pick n cursor)) s with
        | none => .stuck
        | some (next, logs) =>
          emit_list (logs.map .inl)
            (model_rr n actor step next (cursor + 1) : ctreeW (W ⊕ Nat) B X) := by
  rw [unfold_model_rr]
  refine sb_vis (E := writerE (W ⊕ Nat)) _ fun _ => ?_
  split
  · exact sbisim_refl _
  · exact emit_list_sbisim _ (sb_guard _)

/-- Round-robin model congruence in the state (through any relation `R` the step respects) and
in the cursor modulo the pool size. -/
theorem model_rr_equ (R : St → St → Prop)
    (hstep : ∀ a s t, R s t →
      Option.Rel (fun p q => R p.1 q.1 ∧ p.2 = q.2) (step a s) (step a t)) :
    ∀ s t cursor cursor', R s t → cursor % (n + 1) = cursor' % (n + 1) →
      (model_rr n actor step s cursor : ctreeW (W ⊕ Nat) B X) =
        model_rr n actor step t cursor' := by
  intro s t cursor cursor' hst hmod
  refine eq_coind_upto (fun a b => ∃ (logs : List (W ⊕ Nat)) (g : Bool) (s t : St) (c c' : Nat),
      R s t ∧ c % (n + 1) = c' % (n + 1) ∧
      a = emit_list logs
        (bif g then .guard (model_rr n actor step s c) else model_rr n actor step s c) ∧
      b = emit_list logs
        (bif g then .guard (model_rr n actor step t c') else model_rr n actor step t c'))
    ?_ _ _ ⟨[], false, s, t, cursor, cursor', hst, hmod, rfl, rfl⟩
  rintro _ _ ⟨logs, g, s, t, c, c', hst, hmod, rfl, rfl⟩
  match logs, g with
  | o :: logs, g =>
    simp only [emit_list_cons, unfold_vis]
    exact .vis _ fun _ => .inl ⟨logs, g, s, t, c, c', hst, hmod, rfl, rfl⟩
  | [], true =>
    simp only [emit_list_nil, Bool.cond_true, unfold_guard]
    exact .guard (.inl ⟨[], false, s, t, c, c', hst, hmod, rfl, rfl⟩)
  | [], false =>
    have hnext : (c + 1) % (n + 1) = (c' + 1) % (n + 1) := by
      rw [Nat.add_mod, hmod, ← Nat.add_mod]
    simp only [emit_list_nil, Bool.cond_false]
    rw [unfold_model_rr n actor step s c, unfold_model_rr n actor step t c', rr_pick_mod_congr hmod,
      unfold_vis, unfold_vis]
    refine .vis _ fun _ => ?_
    have hr := hstep (actor (rr_pick n c')) s t hst
    revert hr
    generalize step (actor (rr_pick n c')) s = os
    generalize step (actor (rr_pick n c')) t = ot
    intro hr
    cases hr with
    | none => exact .inr rfl
    | some h =>
      rename_i p q
      obtain ⟨sn, ln⟩ := p
      obtain ⟨tn, tl⟩ := q
      obtain ⟨hr, rfl⟩ := h
      exact .inl ⟨ln.map .inl, true, sn, tn, c + 1, c' + 1, hr, hnext, rfl, rfl⟩

end ModelRR

/-! ## Finite replay against the models -/

/-- The actions round robin selects for `len` turns from `cursor`. -/
def rr_script {Act : Type u} (n : Nat) (actor : Fin (n + 1) → Act) (cursor len : Nat) : List Act :=
  (List.range' cursor len).map fun k => actor (rr_pick n k)

/-- The observable word of a round-robin turn. -/
def rr_turn_obs {W : Type} (n cursor : Nat) (logs : List W) : List (W ⊕ Nat) :=
  .inr (slot_index (rr_pick n cursor)) :: logs.map .inl

/-- The observable word of a finite round-robin run. -/
def rr_run_obs {W : Type} (n cursor : Nat) : List (List W) → List (W ⊕ Nat)
  | [] => []
  | logs :: rest => rr_turn_obs n cursor logs ++ rr_run_obs n (cursor + 1) rest

theorem rr_run_obs_nil_iff {W : Type} (n cursor : Nat) (turns : List (List W)) :
    rr_run_obs n cursor turns = [] ↔ turns = [] := by
  cases turns <;> simp [rr_run_obs, rr_turn_obs]

theorem in_rr_run_obs {W : Type} (n cursor : Nat) (turns : List (List W)) (o : W) :
    o ∈ turns.flatten → .inl o ∈ rr_run_obs n cursor turns := by
  induction turns generalizing cursor with
  | nil => simp
  | cons logs rest ih =>
    intro h
    simp only [List.flatten_cons, List.mem_append] at h
    simp only [rr_run_obs, rr_turn_obs, List.cons_append, List.mem_cons, List.mem_append,
      List.mem_map]
    rcases h with h | h
    · exact .inr (.inl ⟨o, h, rfl⟩)
    · exact .inr (.inr (ih (cursor + 1) h))

section ModelReplay
variable {St Act W X : Type} {B : Effect.{0}} (n : Nat) (actor : Fin (n + 1) → Act)
  (step : Act → St → Option (St × List W))

theorem model_rr_run_turns : ∀ len cursor s last turns,
    run_turns step (fun xs => [xs]) (rr_script n actor cursor len) s = some (last, turns) →
    (model_rr n actor step s cursor : ctreeW (W ⊕ Nat) B X) ~
      emit_list (rr_run_obs n cursor turns)
        (model_rr n actor step last (cursor + len) : ctreeW (W ⊕ Nat) B X) := by
  intro len
  induction len with
  | zero =>
    intro cursor s last turns hrun
    simp only [rr_script, List.range'_zero, List.map_nil, run_turns, Option.some.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact sbisim_refl _
  | succ len ih =>
    intro cursor s last turns hrun
    simp only [rr_script, List.range'_succ, List.map_cons, run_turns] at hrun
    split at hrun
    · simp at hrun
    · rename_i next event hstep
      split at hrun
      · simp at hrun
      · rename_i last' tail hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        have := ih (cursor + 1) next last' tail hrest
        rw [Nat.add_right_comm] at this
        rw [unfold_model_rr, hstep]
        simp only [rr_run_obs, rr_turn_obs, List.cons_append,
          emit_list_cons, emit_list_app]
        exact sb_vis (E := writerE (W ⊕ Nat)) _ fun _ =>
          emit_list_sbisim _ (sb_guard_l this)

end ModelReplay

theorem label_logs_app {W : Type u} (xs ys : List (Label (writerE W))) :
    label_logs (xs ++ ys) = label_logs xs ++ label_logs ys := by
  simp [label_logs, List.flatMap_append]

theorem label_taus_app {W : Type u} (xs ys : List (Label (writerE W))) :
    label_taus (xs ++ ys) = label_taus xs + label_taus ys := by
  simp [label_taus, List.filter_append]

section ModelReplayND
variable {St Act W X : Type} {B : Effect.{0}} [Bn -< B] [LawfulSubeffect Bn B] (n : Nat)
  (actor : Fin (n + 1) → Act) (step : Act → St → Option (St × List W))
  (slot : Act → Fin (n + 1)) (actor_slot : ∀ who, actor (slot who) = who)
include actor_slot

/-- Replaying a script against the ND model: realizing every abstract action needs the inverse
slot law. -/
theorem model_run_turns_labels : ∀ (script : List Act) s last logs,
    run_turns step (fun xs => xs) script s = some (last, logs) →
    ∃ labels residual,
      run_turns step turn_labels script s = some (last, labels) ∧
      label_logs labels = logs ∧
      label_taus labels = script.length ∧
      FiniteSteps (model_nd n actor step s : ctreeW W B X) labels residual ∧
      residual ~ (model_nd n actor step last : ctreeW W B X) := by
  intro script
  induction script with
  | nil =>
    intro s last logs hrun
    simp only [run_turns, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨[], model_nd n actor step s, rfl, rfl, rfl, .nil _, sbisim_refl _⟩
  | cons who rest ih =>
    intro s last logs hrun
    simp only [run_turns] at hrun
    split at hrun
    · simp at hrun
    · rename_i next event hstep
      split at hrun
      · simp at hrun
      · rename_i last' logs' hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨labels, residual, hlabels, hlogs, htaus, hsteps, eres⟩ := ih next last' logs' hrest
        obtain ⟨residual', hsteps', eres'⟩ := finite_steps_sbisim hsteps _
          (sbisim_symm (sb_guard (model_nd n actor step next : ctreeW W B X)))
        refine ⟨turn_labels event ++ labels, residual', ?_, ?_, ?_, ?_, ?_⟩
        · simp [run_turns, hstep, hlabels]
        · rw [label_logs_app, label_logs_turn_labels, hlogs]
        · rw [label_taus_app, label_taus_turn_labels, htaus, List.length_cons, Nat.add_comm]
        · exact finite_steps_app (model_turn_finite_steps n actor step (slot who) s next event
            (by rw [actor_slot]; exact hstep)) hsteps'
        · exact sbisim_trans (sbisim_symm eres') eres

end ModelReplayND

/-! ## Round-robin recurrence from finite cycle certificates

A family of boundaries, each of whose RR cycle actually runs to a state related to the next
boundary while producing a nonempty turn batch, makes the RR model bisimilar to the logged batch
loop `emit_batches`. -/

theorem model_rr_emit_batches {St Act W X I : Type} {B : Effect.{0}} (n : Nat)
    (actor : Fin (n + 1) → Act) (step : Act → St → Option (St × List W)) (R : St → St → Prop)
    (hstep : ∀ a s t, R s t →
      Option.Rel (fun p q => R p.1 q.1 ∧ p.2 = q.2) (step a s) (step a t))
    (boundary : I → St) (batch : I → List (List W)) (next : I → I) (Inv : I → Prop)
    (cursor period : Nat) (hcursor : (cursor + period) % (n + 1) = cursor % (n + 1))
    (hnext : ∀ i, Inv i → Inv (next i)) (hnonempty : ∀ i, Inv i → batch i ≠ [])
    (hcycle : ∀ i, Inv i → ∃ last,
      run_turns step (fun xs => [xs]) (rr_script n actor cursor period) (boundary i) =
        some (last, batch i) ∧ R last (boundary (next i))) :
    ∀ i, Inv i → (model_rr n actor step (boundary i) cursor : ctreeW (W ⊕ Nat) B X) ~
      (emit_batches (fun j => rr_run_obs n cursor (batch j)) next i : ctreeW (W ⊕ Nat) B X) := by
  refine emit_batches_bisim (fun j => rr_run_obs n cursor (batch j)) next Inv
    (fun i => model_rr n actor step (boundary i) cursor) hnext
    (fun i hi hnil => hnonempty i hi ((rr_run_obs_nil_iff n cursor (batch i)).1 hnil)) ?_
  intro i hi
  obtain ⟨last, hrun, hlast⟩ := hcycle i hi
  refine sbisim_trans
    (model_rr_run_turns n actor step period cursor (boundary i) last (batch i) hrun)
    (emit_list_sbisim _ ?_)
  rw [model_rr_equ n actor step R hstep last (boundary (next i)) (cursor + period) cursor hlast
    hcursor]
  exact sbisim_refl _

/-! ## Realizing an abstract execution by its model -/

theorem valid_execution_realizes_model {St Act W X : Type} {B : Effect.{0}} [Bn -< B]
    [LawfulSubeffect Bn B] (n : Nat) (actor : Fin (n + 1) → Act)
    (step : Act → St → Option (St × List W)) (slot : Act → Fin (n + 1))
    (actor_slot : ∀ who, actor (slot who) = who) (initial : St → Prop)
    (e : Execution St Act (List W)) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e →
    ∀ k (t : ctreeW W B X), t ~ (model_nd n actor step (e.states k) : ctreeW W B X) →
      realizes (fun j => turn_labels (e.emitted j)) k t := by
  intro hvalid
  refine realizes_from_steps _ (fun j => (model_nd n actor step (e.states j) : ctreeW W B X))
    (fun j => turn_labels_nonempty _) fun j => ⟨.guard (model_nd n actor step (e.states (j + 1))),
      model_turn_finite_steps n actor step (slot (e.selected j)) _ _ _ ?_, sb_guard _⟩
  rw [actor_slot]
  exact execution_step step initial e j hvalid

/-! ## Raw scheduled executions

A raw execution is the same `Execution` record, at state `Pool E B (n+1) × Sg`, action `Act` and
output `List W`. -/

section RawExecution
variable {E B : Effect.{0}} {W Sg Act : Type} (n : Nat)
  (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e)) (slot : Act → Fin (n + 1))

/-- One raw turn: the selected slot runs its first-yield segment, the rest of the pool stays. -/
def pool_step (who : Act) (p : Pool E B (n + 1) × Sg) (logs : List W)
    (q : Pool E B (n + 1) × Sg) : Prop :=
  ∃ residual, ThreadSegment handler (fun _ t u => t ~ u) p.1[slot who] p.2 logs residual q.2 ∧
    pool_equ q.1 (p.1.set (slot who) residual)

def pool_execution_valid (ts0 : Pool E B (n + 1)) (σ0 : Sg)
    (se : Execution (Pool E B (n + 1) × Sg) Act (List W)) : Prop :=
  execution_valid (pool_step n handler slot) (fun p => pool_equ p.1 ts0 ∧ p.2 = σ0) se

theorem pool_step_branchfree (who : Act) (ts : Pool E B (n + 1)) (σ : Sg) (logs : List W)
    (ts' : Pool E B (n + 1)) (σ' : Sg) (h : pool_step n handler slot who (ts, σ) logs (ts', σ'))
    (hbf : ∀ j : Fin (n + 1), BranchFree ts[j]) : ∀ j : Fin (n + 1), BranchFree ts'[j] := by
  obtain ⟨residual, hseg, hpool⟩ := h
  intro j
  rw [hpool j]
  by_cases hj : j = slot who
  · subst hj
    simpa using ThreadSegment_branchfree handler _ _ _ _ _ _ hseg (hbf _)
  · rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (fun h => hj (Fin.ext h.symm))]
    exact hbf j

/-- Every raw turn is one silent scheduler choice followed by its logs. -/
theorem valid_pool_execution_scheduler_steps [Bn -< B] [LawfulSubeffect Bn B]
    (se : Execution (Pool E B (n + 1) × Sg) Act (List W)) (ts0 : Pool E B (n + 1)) (σ0 : Sg)
    (k : Nat) (h : pool_execution_valid n handler slot ts0 σ0 se) :
    ∃ next, FiniteSteps (interp_schedule_nd handler (n + 1) (se.states k).1 none (se.states k).2)
        (.tau :: (se.emitted k).map fun o => .obs (E := writerE W) o ⟨⟩) next ∧
      next ~
        interp_schedule_nd handler (n + 1) (se.states (k + 1)).1 none (se.states (k + 1)).2 := by
  obtain ⟨residual, hseg, hpool⟩ := h.2 k
  exact segment_scheduler_steps handler (fun _ t u => t ~ u) (fun _ _ _ h => h) _ _ _ _ residual _ _
    hseg hpool

end RawExecution

/-! ## Pool simulation

A proof-only certificate (not a typeclass) packaging exactly: executable totality and invariant
preservation, the actual handler-backed first-yield segment of the selected slot, and stability of
the unselected slots. It assumes no liveness, fairness, model trace, global bisimulation, or
function equality of states. -/

structure PoolSimulation {E B : Effect.{0}} {W Sg St Act : Type} (n : Nat)
    (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e)) (slot : Act → Fin (n + 1))
    (step : Act → St → Option (St × List W)) (pool_of : St → Pool E B (n + 1))
    (agree : Sg → St → Prop) (Inv : St → Prop) : Prop where
  simulation_total : ∀ who s, Inv s → ∃ s' event, step who s = some (s', event) ∧ Inv s'
  simulation_segment : ∀ who s s' event σ, Inv s → agree σ s → step who s = some (s', event) →
    ∃ residual σ',
      ThreadSegment handler (fun _ t u => t = u) (pool_of s)[slot who] σ event residual σ' ∧
      agree σ' s' ∧ guard_equ residual (pool_of s')[slot who] ∧
      ∀ j, j ≠ slot who → (pool_of s)[j] = (pool_of s')[j]

section PoolSimulationTheory
variable {E B : Effect.{0}} {W Sg St Act : Type} {n : Nat}
  {handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e)} {slot : Act → Fin (n + 1)}
  {step : Act → St → Option (St × List W)} {pool_of : St → Pool E B (n + 1)}
  {agree : Sg → St → Prop} {Inv : St → Prop}
  (Hsim : PoolSimulation n handler slot step pool_of agree Inv)
include Hsim

/-- The certificate transported to any pool aligned up to finitely many leading guards. -/
theorem selected_turn_segment (ts : Pool E B (n + 1)) (s : St) (who : Act) (s' : St)
    (event : List W) (σ : Sg) (hinv : Inv s) (hagree : agree σ s)
    (hpool : pool_guard_equ ts (pool_of s)) (hstep : step who s = some (s', event)) :
    ∃ residual σ',
      ThreadSegment handler (fun _ t u => t = u) ts[slot who] σ event residual σ' ∧
      agree σ' s' ∧ pool_guard_equ (ts.set (slot who) residual) (pool_of s') := by
  obtain ⟨residual, σ', hseg, hagree', htail, hframe⟩ :=
    Hsim.simulation_segment who s s' event σ hinv hagree hstep
  refine ⟨residual, σ',
    (guard_equ_segment_iff handler _ _ _ (hpool (slot who)) σ event residual σ').2 hseg,
    hagree', ?_⟩
  intro j
  by_cases hj : j = slot who
  · subst hj; simpa using htail
  · rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (fun h => hj (Fin.ext h.symm))]
    exact guard_equ_trans _ _ _ (hpool j) (guard_equ_equ _ _ (hframe j hj))

/-- One model turn at a guard-aligned pool, run by the ND scheduler focused on the selected
slot. -/
theorem pool_simulation_turn_nd [Bn -< B] (ts : Pool E B (n + 1)) (s : St) (who : Act) (s' : St)
    (event : List W) (σ : Sg) (hinv : Inv s) (hagree : agree σ s)
    (hpool : pool_guard_equ ts (pool_of s)) (hstep : step who s = some (s', event)) :
    ∃ residual σ', agree σ' s' ∧ pool_guard_equ (ts.set (slot who) residual) (pool_of s') ∧
      interp_schedule_nd handler (n + 1) ts (some (slot who)) σ ~
        emit_list event
          (interp_schedule_nd handler (n + 1) (ts.set (slot who) residual) none σ') := by
  obtain ⟨residual, σ', hseg, hagree', hpool'⟩ :=
    selected_turn_segment Hsim ts s who s' event σ hinv hagree hpool hstep
  exact ⟨residual, σ', hagree', hpool', segment_interp_nd handler (fun _ t u => t ~ u)
    (fun _ _ _ h => h) n ts (slot who) σ event residual σ'
    (ThreadSegment_mono handler _ _ (fun _ t u h => equ_sbisim t u h) _ _ _ _ _ hseg)⟩

/-- The segment is unique, so the abstract turn determines its logs, its final handler state
(relationally) and the updated pool alignment. -/
theorem selected_segment_deterministic (ts : Pool E B (n + 1)) (s : St) (who : Act) (s' : St)
    (event : List W) (σ : Sg) (logs : List W) (residual : Thread E B) (σ' : Sg) (hinv : Inv s)
    (hagree : agree σ s) (hpool : pool_guard_equ ts (pool_of s))
    (hstep : step who s = some (s', event))
    (hseg : ThreadSegment handler (fun _ t u => t ~ u) ts[slot who] σ logs residual σ') :
    logs = event ∧ agree σ' s' ∧ pool_guard_equ (ts.set (slot who) residual) (pool_of s') := by
  obtain ⟨r0, σ0, hseg0, hagree0, hpool0⟩ :=
    selected_turn_segment Hsim ts s who s' event σ hinv hagree hpool hstep
  obtain ⟨rfl, rfl, rfl⟩ := ThreadSegment_deterministic handler (fun _ t u => t ~ u)
    (fun _ _ _ h => h) _ σ logs residual σ' event r0 σ0 hseg
    (ThreadSegment_mono handler _ _ (fun _ t u h => equ_sbisim t u h) _ _ _ _ _ hseg0)
  exact ⟨rfl, hagree0, hpool0⟩

/-- Every raw segment of the selected slot is some model turn. -/
theorem selected_segment_complete (ts : Pool E B (n + 1)) (s : St) (who : Act) (σ : Sg)
    (logs : List W) (residual : Thread E B) (σ' : Sg) (hinv : Inv s) (hagree : agree σ s)
    (hpool : pool_guard_equ ts (pool_of s))
    (hseg : ThreadSegment handler (fun _ t u => t ~ u) ts[slot who] σ logs residual σ') :
    ∃ s' event, step who s = some (s', event) ∧ Inv s' ∧ logs = event ∧ agree σ' s' ∧
      pool_guard_equ (ts.set (slot who) residual) (pool_of s') := by
  obtain ⟨s', event, hstep, hinv'⟩ := Hsim.simulation_total who s hinv
  exact ⟨s', event, hstep, hinv', selected_segment_deterministic Hsim ts s who s' event σ logs
    residual σ' hinv hagree hpool hstep hseg⟩

/-! ### Worker guarantees of an aligned pool

Every slot reaches its next yield; no slot is finished, forking, branching, stepping, stuck,
divergent, or at a faulting handler call. -/

theorem pool_simulation_worker_segment (ts : Pool E B (n + 1)) (s : St) (who : Act) (σ : Sg)
    (hinv : Inv s) (hagree : agree σ s) (hpool : pool_guard_equ ts (pool_of s)) :
    ∃ event residual σ',
      ThreadSegment handler (fun _ t u => t ~ u) ts[slot who] σ event residual σ' := by
  obtain ⟨s', event, hstep, -⟩ := Hsim.simulation_total who s hinv
  obtain ⟨residual, σ', hseg, -, -⟩ :=
    selected_turn_segment Hsim ts s who s' event σ hinv hagree hpool hstep
  exact ⟨event, residual, σ',
    ThreadSegment_mono handler _ _ (fun _ t u h => equ_sbisim t u h) _ _ _ _ _ hseg⟩

theorem pool_simulation_no_terminal_prefix (ts : Pool E B (n + 1)) (s : St) (who : Act) (σ : Sg)
    (hinv : Inv s) (hagree : agree σ s) (hpool : pool_guard_equ ts (pool_of s)) :
    ¬ guard_equ ts[slot who] (pure ⟨⟩) ∧
    (∀ k : Bool → Thread E B, ¬ guard_equ ts[slot who] (.vis (.inr (.inl ⟨⟩)) k)) ∧
    (∀ (c : B.I) (k : B.O c → Thread E B), ¬ guard_equ ts[slot who] (.br c k)) ∧
    (∀ u, ¬ guard_equ ts[slot who] (.step u)) ∧
    ¬ guard_equ ts[slot who] (.stuck : Thread E B) := by
  obtain ⟨event, residual, σ', hseg⟩ :=
    pool_simulation_worker_segment Hsim ts s who σ hinv hagree hpool
  refine ⟨fun hbad => ?_, fun k hbad => ?_, fun c k hbad => ?_, fun v hbad => ?_,
    fun hbad => ?_⟩ <;>
    obtain ⟨u, hf, -⟩ := guard_equ_segment handler _ _ _ _ _ _ _ hbad hseg
  · exact ThreadSegment_ret_absurd handler _ σ _ u σ' hf
  · exact ThreadSegment_fork_absurd handler _ k σ _ u σ' hf
  · exact ThreadSegment_br_absurd handler _ c k σ _ u σ' hf
  · exact ThreadSegment_step_absurd handler _ v σ _ u σ' hf
  · exact ThreadSegment_stuck_absurd handler _ σ _ u σ' hf

theorem pool_simulation_no_fault_or_divergence (ts : Pool E B (n + 1)) (s : St) (who : Act)
    (σ : Sg) (hinv : Inv s) (hagree : agree σ s) (hpool : pool_guard_equ ts (pool_of s)) :
    ¬ isStuck ts[slot who] ∧ ¬ guard_equ ts[slot who] (CTree.spinS : Thread E B) ∧
    ∀ (e : E.I) (k : E.O e → Thread E B), guard_equ ts[slot who] (.vis (.inr (.inr e)) k) →
      ¬ (handler e σ ~ (.stuck : ctreeW W B (E.O e × Sg))) := by
  obtain ⟨event, residual, σ', hseg⟩ :=
    pool_simulation_worker_segment Hsim ts s who σ hinv hagree hpool
  refine ⟨fun hstuck => ThreadSegment_divergent_absurd handler _ _ _ _ _ _ hstuck hseg,
    fun hbad => ?_, fun e k hhead hfault => ?_⟩
  · obtain ⟨u, hf, -⟩ := guard_equ_segment handler _ _ _ _ _ _ _ hbad hseg
    exact ThreadSegment_spin_absurd handler _ σ _ u σ' hf
  · obtain ⟨u, hf, -⟩ := guard_equ_segment handler _ _ _ _ _ _ _ hhead hseg
    exact ThreadSegment_fault_absurd handler _ (fun _ _ _ h => h) e k σ _ u σ' hfault hf

/-! ### Alignment of raw executions with model executions

Any valid raw execution and any valid model execution making the same selections stay aligned at
every index: invariant, relational state agreement, guard-aligned pools and equal observations. -/

theorem source_execution_complete (ts0 : Pool E B (n + 1)) (σ0 : Sg) (s0 : St)
    (se : Execution (Pool E B (n + 1) × Sg) Act (List W)) (e : Execution St Act (List W))
    (hinv0 : Inv s0) (hagree0 : agree σ0 s0) (hpool0 : pool_guard_equ ts0 (pool_of s0))
    (hse : pool_execution_valid n handler slot ts0 σ0 se)
    (he : execution_valid (fun a s o s' => step a s = some (s', o)) (fun s => s = s0) e)
    (hsel : ∀ k, e.selected k = se.selected k) :
    ∀ k, Inv (e.states k) ∧ agree (se.states k).2 (e.states k) ∧
      pool_guard_equ (se.states k).1 (pool_of (e.states k)) ∧ se.emitted k = e.emitted k := by
  obtain ⟨⟨hp, hs⟩, hsteps⟩ := hse
  obtain ⟨he0, hestep⟩ := he
  have he0 : e.states 0 = s0 := he0
  have aligned : ∀ k, Inv (e.states k) ∧ agree (se.states k).2 (e.states k) ∧
      pool_guard_equ (se.states k).1 (pool_of (e.states k)) := by
    intro k
    induction k with
    | zero => rw [he0, hs]; exact ⟨hinv0, hagree0, pool_equ_guard_trans _ _ _ hp hpool0⟩
    | succ k ih =>
      obtain ⟨hinv, hagree, hpool⟩ := ih
      obtain ⟨residual, hseg, epool⟩ := hsteps k
      obtain ⟨s', event, hstep, hinv', -, hagree', hpool'⟩ := selected_segment_complete Hsim _
        (e.states k) (se.selected k) _ _ residual _ hinv hagree hpool hseg
      rw [← hsel k, hestep k, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨hinv', hagree', pool_equ_guard_trans _ _ _ epool hpool'⟩
  intro k
  obtain ⟨hinv, hagree, hpool⟩ := aligned k
  obtain ⟨residual, hseg, -⟩ := hsteps k
  exact ⟨hinv, hagree, hpool, (selected_segment_deterministic Hsim _ (e.states k) (se.selected k)
    (e.states (k + 1)) (e.emitted k) _ _ residual _ hinv hagree hpool (hsel k ▸ hestep k) hseg).1⟩

/-- Every finitely reachable raw configuration is aligned with some model state. -/
theorem pool_simulation_reachable (ts0 : Pool E B (n + 1)) (σ0 : Sg) (s0 : St) (hinv0 : Inv s0)
    (hagree0 : agree σ0 s0) (hpool0 : pool_guard_equ ts0 (pool_of s0)) :
    ∀ ts σ, reachable (pool_step n handler slot) (fun p => pool_equ p.1 ts0 ∧ p.2 = σ0) (ts, σ) →
      ∃ s, Inv s ∧ agree σ s ∧ pool_guard_equ ts (pool_of s) := by
  intro ts σ h
  refine reachable_inv (pool_step n handler slot) _
    (fun p => ∃ s, Inv s ∧ agree p.2 s ∧ pool_guard_equ p.1 (pool_of s)) ?_ ?_ (ts, σ) h
  · rintro ⟨ts1, σ1⟩ ⟨hp, rfl⟩
    exact ⟨s0, hinv0, hagree0, pool_equ_guard_trans _ _ _ hp hpool0⟩
  · rintro a ⟨ts1, σ1⟩ o ⟨ts2, σ2⟩ ⟨s, hinv, hagree, hpool⟩ ⟨residual, hseg, epool⟩
    obtain ⟨s', -, -, hinv', -, hagree', hpool'⟩ :=
      selected_segment_complete Hsim ts1 s a σ1 o residual σ2 hinv hagree hpool hseg
    exact ⟨s', hinv', hagree', pool_equ_guard_trans _ _ _ epool hpool'⟩

/-! ### Nondeterministic scheduling agrees with the ND model -/

theorem pool_simulation_nd_bisim [Bn -< B] [LawfulSubeffect Bn B] (actor : Fin (n + 1) → Act)
    (slot_actor : ∀ i, slot (actor i) = i) :
    ∀ s ts σ, Inv s → agree σ s → pool_guard_equ ts (pool_of s) →
      interp_schedule_nd handler (n + 1) ts none σ ~
        (model_nd n actor step s : ctreeW W B (PUnit × Sg)) := by
  intro s ts σ hinv hagree hpool
  refine coinduction (b := sb Eq) (ι := {p : St × Pool E B (n + 1) × Sg //
      Inv p.1 ∧ agree p.2.2 p.1 ∧ pool_guard_equ p.2.1 (pool_of p.1)})
    (fun p => interp_schedule_nd handler (n + 1) p.1.2.1 none p.1.2.2)
    (fun p => (model_nd n actor step p.1.1 : ctreeW W B (PUnit × Sg))) ?_
    ⟨(s, ts, σ), hinv, hagree, hpool⟩
  rintro R hR cih ⟨⟨s, ts, σ⟩, hinv, hagree, hpool⟩
  dsimp only
  refine sbisim_clos_sb (.step hR) _ _ _ _ (interp_schedule_nd_select handler n ts σ) ?_
    (sbisim_refl _)
  rw [unfold_model_nd]
  refine step_sb_brSn_id fun i => ?_
  obtain ⟨next, event, hstep, hnextinv⟩ := Hsim.simulation_total (actor i) s hinv
  obtain ⟨residual, σ', hagree', hnextpool, efocus⟩ :=
    pool_simulation_turn_nd Hsim ts s (actor i) next event σ hinv hagree hpool hstep
  simp only [slot_actor] at hnextpool efocus
  rw [hstep]
  refine sbisim_clos_sb hR _ _ _ _ efocus (emit_list_chain hR event ?_) (sbisim_refl _)
  exact sbisim_clos_sb hR _ _ _ _ (sbisim_refl _)
    (cih ⟨(next, ts.set i residual, σ'), hnextinv, hagree', hnextpool⟩) (sbisim_symm (sb_guard _))

end PoolSimulationTheory

/-! ### Round-robin scheduling agrees with the RR model

The logged round-robin runner uses the finite branch signature `Bn`. -/

theorem pool_simulation_rr_bisim {E : Effect.{0}} {W Sg St Act : Type} {n : Nat}
    {handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)} (actor : Fin (n + 1) → Act)
    {slot : Act → Fin (n + 1)} (slot_actor : ∀ i, slot (actor i) = i)
    {step : Act → St → Option (St × List W)} {pool_of : St → Pool E Bn (n + 1)}
    {agree : Sg → St → Prop} {Inv : St → Prop}
    (Hsim : PoolSimulation n handler slot step pool_of agree Inv) :
    ∀ s ts σ cursor, Inv s → agree σ s → pool_guard_equ ts (pool_of s) →
      interp_schedule_rr handler (n + 1) ts none cursor σ ~
        (model_rr n actor step s cursor : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) := by
  intro s ts σ cursor hinv hagree hpool
  refine coinduction (b := sb Eq) (ι := {p : St × Pool E Bn (n + 1) × Sg × Nat //
      Inv p.1 ∧ agree p.2.2.1 p.1 ∧ pool_guard_equ p.2.1 (pool_of p.1)})
    (fun p => interp_schedule_rr handler (n + 1) p.1.2.1 none p.1.2.2.2 p.1.2.2.1)
    (fun p => (model_rr n actor step p.1.1 p.1.2.2.2 : ctreeW (W ⊕ Nat) Bn (PUnit × Sg))) ?_
    ⟨(s, ts, σ, cursor), hinv, hagree, hpool⟩
  rintro R hR cih ⟨⟨s, ts, σ, cursor⟩, hinv, hagree, hpool⟩
  dsimp only
  obtain ⟨next, event, hstep, hnextinv⟩ :=
    Hsim.simulation_total (actor (rr_pick n cursor)) s hinv
  obtain ⟨residual, σ', hseg, hagree', hnextpool⟩ :=
    selected_turn_segment Hsim ts s _ next event σ hinv hagree hpool hstep
  simp only [slot_actor] at hseg hnextpool
  obtain ⟨word, ew, et⟩ := exact_segment_rr_prefix handler n ts (rr_pick n cursor)
    ts[rr_pick n cursor] (cursor + 1) σ event residual σ' hseg
  rw [interp_schedule_rr_equ handler (n + 1) _ ts _ _ _ (pool_replace_current ts _)] at et
  rw [segment_rr_select_exact, unfold_model_rr, hstep]
  refine step_sb_vis_id_gen (E := writerE (W ⊕ Nat)) _ _ _ fun _ => ⟨?_, rfl⟩
  refine sbisim_clos_sb hR _ (emit_list (event.map .inl) (interp_schedule_rr handler (n + 1)
    (ts.set (rr_pick n cursor) residual) none (cursor + 1) σ')) _ _ ?_
    (emit_list_chain hR _ ?_) (sbisim_refl _)
  · rw [et]
    refine sb_guard_l (sbisim_trans (rr_prefix_emit_sbisim word _) ?_)
    rw [ew]
    exact emit_list_sbisim _ (sb_guard _)
  · exact sbisim_clos_sb hR _ _ _ _ (sbisim_refl _)
      (cih ⟨(next, ts.set (rr_pick n cursor) residual, σ', cursor + 1), hnextinv, hagree',
        hnextpool⟩) (sbisim_symm (sb_guard _))

-- Not ported: the section-local `Abbreviation`s `Rexact`/`Rsb` (written inline as
-- `fun _ t u => t = u` / `fun _ t u => t ~ u`).

end Tisl.Yield
