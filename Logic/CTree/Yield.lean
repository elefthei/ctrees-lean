/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Execution
public import Logic.CTree.TraceRules
public import Logic.CTree.EF
public import Logic.Yield.SBisimSchedule

/-!
# TICL rules for instrumented raw threads and scheduled pools

Rules over raw ctrees built from `yieldE`, `forkE` and state events: standalone threads under a
state handler, singleton scheduler reductions, turn-structured emission (`emit_turns`), the
round-robin recurrence from executable cycle certificates, structural invariance/eventuality over
yielding pools (`ClosedTurns`, `RankedTurns`), and the exact normal forms of returning pools
(← `CTree/Logic/Yield.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction Notation
open ITree (Effect)

/-! ## Visible `Bn` branching

`brSn` is a `brS` over the embedded `Bn` arity; with a lawful embedding every alternative is
reachable. -/

section BrSn
variable {E B : Effect.{0}} [Bn -< B] [LawfulSubeffect Bn B] {X : Type} {w w' : World E}

private theorem bn_reach (n : Nat) (j : Fin n) :
    ∃ y, ((ITree.Subeffect.map (E₁ := Bn) (E₂ := B) (⟨n⟩ : Bn.I)).2 y).down = j :=
  let ⟨y, hy⟩ := LawfulSubeffect.map_surj (E₁ := Bn) (E₂ := B) (⟨n⟩ : Bn.I) ⟨j⟩
  ⟨y, by rw [hy]⟩

private theorem ktrans_brSn {n : Nat} {k : Fin n → CTree E B X} {t' : CTree E B X} :
    ktrans (CTree.brSn n k) w t' w' ↔ ∃ j, t' = k j ∧ w = w' ∧ NotDone w := by
  refine (ktrans_brS (c := (ITree.Subeffect.map (E₁ := Bn) (E₂ := B) (⟨n⟩ : Bn.I)).1)).trans
    ⟨fun ⟨y, h⟩ => ⟨_, h⟩, fun ⟨j, h⟩ => ?_⟩
  obtain ⟨y, rfl⟩ := bn_reach (B := B) n j
  exact ⟨y, h⟩

private theorem can_step_brSn {n : Nat} {k : Fin (n + 1) → CTree E B X} :
    can_step (CTree.brSn (n + 1) k) w ↔ NotDone w :=
  ⟨can_step_not_done, fun hd =>
    let ⟨y, _⟩ := bn_reach (B := B) (n + 1) 0
    (can_step_brS (c := (ITree.Subeffect.map (E₁ := Bn) (E₂ := B) (⟨n + 1⟩ : Bn.I)).1) y).2 hd⟩

end BrSn

/-! ## Rules for raw threads under an arbitrary state handler -/

section ThreadStateRules
variable {E B : Effect.{0}} {W S : Type} (h : (e : E.I) → StateT S (ctreeW W B) (E.O e))

theorem axr_ithread_ret {X : Type} (r : X) (s : S) (w : World (writerE W))
    (R : X × S → World (writerE W) → Prop) :
    NotDone w → R (r, s) w →
      entails (.ret R)
        (interp_state h (interp_thread (pure r : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X)) s) w :=
  fun hd hR => by rw [interp_state_thread_ret]; exact ret_ret hd hR

theorem anr_ithread_bind_r_eq {A C : Type} (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B A)
    (k : A → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B C) (s s' : S) (r : A) (w w' : World (writerE W))
    (φ : TiclL (writerE W)) (ψ : TiclR (writerE W) (C × S)) :
    entails (ret= (r, s') w') (interp_state h (interp_thread t) s) w →
    entails (φ AN ψ) (interp_state h (interp_thread (k r)) s') w' →
    entails (φ AN ψ) (interp_state h (interp_thread (t >>= k)) s) w :=
  fun ht hk => by rw [interp_state_thread_bind]; exact ticl_bind_ret_eq ht hk

theorem au_ithread_bind_r_eq {A C : Type} {i : Option Type}
    (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B A) (k : A → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B C)
    (s s' : S) (r : A) (w w' : World (writerE W)) (φ : TiclL (writerE W))
    (ψ : Ticl (writerE W) i) :
    entails (φ AU ret= (r, s') w') (interp_state h (interp_thread t) s) w →
    entails (φ AU ψ) (interp_state h (interp_thread (k r)) s') w' →
    entails (φ AU ψ) (interp_state h (interp_thread (t >>= k)) s) w :=
  fun ht hk => by rw [interp_state_thread_bind]; exact u_bind_r_eq ht hk

end ThreadStateRules

/-! ## Singleton scheduler rules under an arbitrary state handler -/

section ScheduleStateRules
variable {E B : Effect.{0}} [Bn -< B] {W S : Type}
  (h : (e : E.I) → StateT S (ctreeW W B) (E.O e))

theorem axr_schedule_nd_ret (s : S) (w : World (writerE W))
    (R : PUnit × S → World (writerE W) → Prop) :
    NotDone w → R (⟨⟩, s) w →
      entails (.ret R) (interp_schedule_nd h 1 #v[(pure ⟨⟩ : Thread E B)] (some 0) s) w :=
  fun hd hR => (proper_entails_meq _ (sbisim_trans
    (interp_schedule_nd_ret h 0 _ 0 s (by simp)) (interp_schedule_nd_empty h _ s))).2
    (ret_ret hd hR)

/-- A cooperative `Yield` costs one visible step: the scheduling pick. -/
theorem axax_schedule_nd_yield [LawfulSubeffect Bn B] (s : S) (w : World (writerE W))
    (R : PUnit × S → World (writerE W) → Prop) :
    NotDone w → R (⟨⟩, s) w →
      entails (AX (.ret R)) (interp_schedule_nd h 1
        #v[(.vis (.inl ⟨⟩) fun _ => pure ⟨⟩ : Thread E B)] (some 0) s) w := by
  intro hd hR
  refine (proper_entails_meq _ (sbisim_trans
    (interp_schedule_nd_yield h 0 _ 0 (fun _ => pure ⟨⟩) s (by simp))
    (interp_schedule_nd_select h 0 _ s))).2
    ⟨ticll_top hd, can_step_brSn.2 hd, fun t' w' tr => ?_⟩
  obtain ⟨j, rfl, rfl, -⟩ := ktrans_brSn.1 tr
  obtain rfl := fin1_eq j
  exact (proper_entails_meq _ (sbisim_trans (interp_schedule_nd_ret h 0 _ 0 s (by simp))
    (interp_schedule_nd_empty h _ s))).2 (ret_ret hd hR)

end ScheduleStateRules

/-! ## Raw thread rules (`h_stateW` instrumentation) -/

section RawThreadRules
variable {B : Effect.{0}}

/-- A finished raw thread terminates in one step with the unchanged state. -/
theorem axr_thread_ret {Sg X : Type} (r : X) (σ : Sg) (w : World (writerE Sg))
    (R : X × Sg → World (writerE Sg) → Prop) :
    NotDone w → R (r, σ) w → entails (.ret R) (instr_thread (B := B) (pure r) σ) w :=
  axr_ithread_ret h_stateW r σ w R

/-- Sequential composition of raw threads, suffix `AN`. -/
theorem anr_thread_bind_r_eq {Sg A C : Type} (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B A)
    (k : A → CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B C) (σ σ' : Sg) (r : A)
    (w w' : World (writerE Sg)) (φ : TiclL (writerE Sg)) (ψ : TiclR (writerE Sg) (C × Sg)) :
    entails (ret= (r, σ') w') (instr_thread t σ) w →
    entails (φ AN ψ) (instr_thread (k r) σ') w' →
    entails (φ AN ψ) (instr_thread (t >>= k) σ) w :=
  anr_ithread_bind_r_eq h_stateW t k σ σ' r w w' φ ψ

/-- Sequential composition preserves an indexed until endpoint. -/
theorem au_thread_bind_r_eq {Sg A C : Type} {i : Option Type}
    (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B A)
    (k : A → CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B C) (σ σ' : Sg) (r : A)
    (w w' : World (writerE Sg)) (φ : TiclL (writerE Sg)) (ψ : Ticl (writerE Sg) i) :
    entails (φ AU ret= (r, σ') w') (instr_thread t σ) w →
    entails (φ AU ψ) (instr_thread (k r) σ') w' →
    entails (φ AU ψ) (instr_thread (t >>= k) σ) w :=
  au_ithread_bind_r_eq h_stateW t k σ σ' r w w' φ ψ

/-- A raw update hands its logged final return to the indexed endpoint. -/
theorem au_thread_update {Sg X : Type} {i : Option Type} (f : Sg → Sg) (r : X) (σ : Sg)
    (w : World (writerE Sg)) (φ : TiclL (writerE Sg)) (ψ : Ticl (writerE Sg) i) :
    entails φ (log (B := B) (f σ)) w →
    entails ψ (pure (r, f σ) : ctreeW Sg B (X × Sg)) (.obs (E := writerE Sg) (f σ) ⟨⟩) →
    entails (φ AU ψ) (instr_thread (B := B)
      (.vis (.inr (.inr StateOp.get)) fun σ0 =>
        .vis (.inr (.inr (StateOp.put (f σ0)))) fun _ => pure r) σ) w := by
  intro hlog hret
  refine (proper_entails_meq _ (sbisim_trans (instr_thread_get _ σ)
    (instr_thread_put (f σ) (fun _ => pure r) σ))).2 ?_
  rw [instr_thread_ret]
  exact au_log (.matchA hret) (ticll_bind_l hlog)

/-! ### Raw singleton scheduler rules -/

variable [Bn -< B]

/-- A finished singleton pool terminates in one step. -/
theorem axr_schedule_ret {Sg : Type} (σ : Sg) (w : World (writerE Sg))
    (R : PUnit × Sg → World (writerE Sg) → Prop) :
    NotDone w → R (⟨⟩, σ) w →
      entails (.ret R) (instr_schedule (B := B) 1
        #v[(pure ⟨⟩ : CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B PUnit)] (some 0) σ) w :=
  axr_schedule_nd_ret h_stateW σ w R

/-- A cooperative `Yield` in a singleton pool costs one visible step: the scheduler picks the
single runnable slot. -/
theorem axax_schedule_yield [LawfulSubeffect Bn B] {Sg : Type} (σ : Sg) (w : World (writerE Sg))
    (R : PUnit × Sg → World (writerE Sg) → Prop) :
    NotDone w → R (⟨⟩, σ) w →
      entails (AX (.ret R)) (instr_schedule (B := B) 1
        #v[(.vis (.inl ⟨⟩) fun _ => pure ⟨⟩ : CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B PUnit)]
        (some 0) σ) w :=
  axax_schedule_nd_yield h_stateW σ w R

/-- A scheduled singleton state update leaves exactly one log; suffix `AU`. -/
theorem aur_schedule_update {Sg : Type} (f : Sg → Sg) (σ : Sg) (w : World (writerE Sg))
    (ψ : TiclL (writerE Sg)) (R : PUnit × Sg → World (writerE Sg) → Prop) :
    entails ψ (log (B := B) (f σ)) w →
    R (⟨⟩, f σ) (.obs (E := writerE Sg) (f σ) ⟨⟩) →
    entails (ψ AU .ret R) (instr_schedule (B := B) 1
      #v[(.vis (.inr (.inr StateOp.get)) fun σ0 =>
          .vis (.inr (.inr (StateOp.put (f σ0)))) fun _ => pure ⟨⟩ :
        CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B PUnit)] (some 0) σ) w := by
  intro hlog hR
  refine (proper_entails_meq _ (interp_schedule_nd_singleton_update f _ σ (by simp))).2 ?_
  exact au_log (.matchA (ret_ret (.obs _ _) hR)) (ticll_bind_l hlog)

/-- A scheduled singleton state update; prefix `AU`. -/
theorem aul_schedule_update {Sg : Type} (f : Sg → Sg) (σ : Sg) (w : World (writerE Sg))
    (ψ φ : TiclL (writerE Sg)) :
    entails ψ (log (B := B) (f σ)) w →
    entails φ (pure (⟨⟩, f σ) : ctreeW Sg B (PUnit × Sg)) (.obs (E := writerE Sg) (f σ) ⟨⟩) →
    entails (ψ AU φ) (instr_schedule (B := B) 1
      #v[(.vis (.inr (.inr StateOp.get)) fun σ0 =>
          .vis (.inr (.inr (StateOp.put (f σ0)))) fun _ => pure ⟨⟩ :
        CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B PUnit)] (some 0) σ) w := by
  intro hlog hret
  refine (proper_entails_meq _ (interp_schedule_nd_singleton_update f _ σ (by simp))).2 ?_
  exact au_log (.matchA hret) (ticll_bind_l hlog)

end RawThreadRules

/-! ## Turn-structured emission -/

theorem f_emit_turns {W : Type u} {B : Effect.{u}} {X : Type u} {i : Option (Type u)}
    (q : Ticlq) (turns : List (List W)) (t : ctreeW W B X) (w : World (writerE W))
    (ψ : Ticl (writerE W) i) :
    NotDone w → entails (.cu q ⊤ ψ) t (after_logs turns.flatten w) →
      entails (.cu q ⊤ ψ) (emit_turns turns t) w := by
  induction turns generalizing w with
  | nil => exact fun _ h => h
  | cons ev rest ih =>
    intro hd h
    rw [List.flatten_cons, after_logs_app] at h
    have h' := f_emit_list q ev _ w ψ hd (ih _ (after_logs_not_done ev hd) h)
    show entails _ (CTree.step (emit_list ev (emit_turns rest t))) w
    cases q
    · exact au_step.1 (.inr ⟨ticll_top hd, h'⟩)
    · exact eu_step.1 (.inr ⟨ticll_top hd, h'⟩)

/-! ## Recurrence for repeating turn batches

The turn-structured twin of `emit_batches_agaf`: every turn is one visible `step` followed by its
finite observation list. -/

section EmitTurnBatches
variable {W I X : Type u} {B : Effect.{u}}

theorem af_emit_turns {Y : Type u} (P : W → Prop) (turns : List (List W)) (t : ctreeW W B Y)
    (w : World (writerE W)) :
    NotDone w → entails (AF (visWₜ P)) t (after_logs turns.flatten w) →
      entails (AF (visWₜ P)) (emit_turns turns t) w :=
  f_emit_turns .A turns t w _

theorem af_emit_turns_member {Y : Type u} (P : W → Prop) (turns : List (List W))
    (t : ctreeW W B Y) (w : World (writerE W)) (o : W) :
    NotDone w → o ∈ turns.flatten → P o → entails (AF (visWₜ P)) (emit_turns turns t) w := by
  induction turns generalizing w with
  | nil => exact fun _ h => nomatch h
  | cons ev rest ih =>
    intro hd hin hp
    show entails _ (CTree.step (emit_list ev (emit_turns rest t))) w
    refine au_step.1 (.inr ⟨ticll_top hd, ?_⟩)
    rcases List.mem_append.1 (List.flatten_cons ▸ hin) with hin | hin
    · exact af_emit_list_member ev _ w P o hd hin hp
    · exact af_emit_list ev _ w P hd (ih _ (after_logs_not_done ev hd) hin hp)

theorem af_emit_turns_ret {Y : Type u} (turns : List (List W)) (r : Y) (w : World (writerE W))
    (Q : Y → World (writerE W) → Prop) :
    NotDone w → Q r (after_logs turns.flatten w) →
      entails (AF (.ret Q)) (emit_turns turns (pure r) : ctreeW W B Y) w :=
  fun hd hQ => f_emit_turns .A turns _ w _ hd (.matchA (ret_ret (after_logs_not_done _ hd) hQ))

theorem emit_turn_batches_af (batch : I → List (List W)) (next : I → I) (Inv : I → Prop)
    (rank : I → Nat) (P : W → Prop) (hnext : ∀ i, Inv i → Inv (next i))
    (hprogress : ∀ i, Inv i → (∃ o, o ∈ (batch i).flatten ∧ P o) ∨ rank (next i) < rank i) :
    ∀ i w, Inv i → NotDone w →
      entails (AF (visWₜ P)) (emit_turn_batches batch next i : ctreeW W B X) w := by
  intro i w hi hd
  refine u_iter_prefix_nat (q := .A) (fun j _ => Inv j) (fun j _ => rank j) hd hi
    fun j v hv hj => ?_
  rcases hprogress j hj with ⟨o, hin, hp⟩ | hlt
  · exact .inl (af_emit_turns_member P _ _ v o hv hin hp)
  · exact .inr (af_emit_turns_ret _ _ v _ hv
      ⟨next j, rfl, after_logs_not_done _ hv, hnext j hj, hlt⟩)

/-- The coinductive invariant: a tree bisimilar to a remaining log prefix, then a remaining turn
suffix of the current batch, then the loop. Each step is a real log or a real turn step. -/
theorem emit_turn_batches_agaf (batch : I → List (List W)) (next : I → I) (Inv : I → Prop)
    (rank : I → Nat) (P : W → Prop) (hnext : ∀ i, Inv i → Inv (next i))
    (hnonempty : ∀ i, Inv i → batch i ≠ [])
    (hprogress : ∀ i, Inv i → (∃ o, o ∈ (batch i).flatten ∧ P o) ∨ rank (next i) < rank i) :
    ∀ i w, Inv i → NotDone w →
      entails (AG (AF (visWₜ P))) (emit_turn_batches batch next i : ctreeW W B X) w := by
  intro i w hi hd
  let L (j : I) : ctreeW W B X := emit_turn_batches batch next j
  refine coinduction (b := agcF (entails (AF (visWₜ P))))
    (ι := {p : ctreeW W B X × World (writerE W) //
      ∃ j logs suffix, Inv j ∧ NotDone p.2 ∧ p.1 ~ emit_list logs (emit_turns suffix (L j))})
    (fun p => p.1.1) (fun p => p.1.2) ?_ ⟨(L i, w), i, [], [], hi, hd, sbisim_refl _⟩
  rintro R - cih ⟨⟨t, v⟩, j, logs, suffix, hj, hv, ht⟩
  have haf : entails (AF (visWₜ P)) t v :=
    (proper_entails_meq _ ht).2 (af_emit_list _ _ v P hv (af_emit_turns P _ _ _
      (after_logs_not_done _ hv) (emit_turn_batches_af batch next Inv rank P hnext hprogress j _
        hj (after_logs_not_done _ (after_logs_not_done _ hv)))))
  cases logs with
  | cons o logs =>
    refine ⟨haf, (proper_can_step ht).2 (can_step_log_bind o hv), fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht tr
    simp only [emit_list_cons] at tr
    obtain ⟨_, hw', rfl, -⟩ := ktrans_vis.1 tr
    exact cih ⟨(t', w'), j, logs, suffix, hj, hw' ▸ .obs _ _, hu⟩
  | nil =>
    obtain ⟨ev, rest, j', hj', ht'⟩ : ∃ ev rest j', Inv j' ∧
        t ~ CTree.step (emit_list ev (emit_turns rest (L j'))) := by
      cases suffix with
      | cons ev rest => exact ⟨ev, rest, j, hj, ht⟩
      | nil =>
        cases hb : batch j with
        | nil => exact absurd hb (hnonempty j hj)
        | cons ev rest =>
          refine ⟨ev, rest, next j, hnext j hj, sbisim_trans ht ?_⟩
          have := emit_turn_batches_unfold_sbisim (B := B) (X := X) batch next j
          rwa [hb] at this
    refine ⟨haf, (proper_can_step ht').2 (can_step_step.2 hv), fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht' tr
    obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
    exact cih ⟨(t', v), j', ev, rest, hj', hv, hu⟩

end EmitTurnBatches

/-! ## Round-robin recurrence from executable cycle certificates

For clients holding finite RR cycle runs rather than a preconstructed log loop: transport through
`model_rr_emit_batches`, then `emit_batches_agaf`. -/

theorem model_rr_agaf {St Act W X I : Type} {B : Effect.{0}} (n : Nat)
    (actor : Fin (n + 1) → Act) (step : Act → St → Option (St × List W)) (R : St → St → Prop)
    (hstep : ∀ a s t, R s t →
      Option.Rel (fun p q => R p.1 q.1 ∧ p.2 = q.2) (step a s) (step a t))
    (boundary : I → St) (batch : I → List (List W)) (next : I → I) (Inv : I → Prop)
    (cursor period : Nat) (hcursor : (cursor + period) % (n + 1) = cursor % (n + 1))
    (hnext : ∀ i, Inv i → Inv (next i)) (hnonempty : ∀ i, Inv i → batch i ≠ [])
    (hcycle : ∀ i, Inv i → ∃ last,
      run_turns step (fun xs => [xs]) (rr_script n actor cursor period) (boundary i) =
        some (last, batch i) ∧ R last (boundary (next i)))
    (rank : I → Nat) (P : W → Prop)
    (hprogress : ∀ i, Inv i → (∃ o, o ∈ (batch i).flatten ∧ P o) ∨ rank (next i) < rank i) :
    ∀ i w, Inv i → NotDone w →
      entails (AG (AF (visWₜ (fair_obs P))))
        (model_rr n actor step (boundary i) cursor : ctreeW (W ⊕ Nat) B X) w := by
  intro i w hi hd
  refine (proper_entails_meq _ (model_rr_emit_batches n actor step R hstep boundary batch next
    Inv cursor period hcursor hnext hnonempty hcycle i hi)).2 ?_
  refine emit_batches_agaf (fun j => rr_run_obs n cursor (batch j)) next Inv rank (fair_obs P)
    hnext (fun j hj hnil => hnonempty j hj ((rr_run_obs_nil_iff n cursor (batch j)).1 hnil))
    (fun j hj => ?_) i w hi hd
  rcases hprogress j hj with ⟨o, hin, hp⟩ | hlt
  · exact .inl ⟨.inl o, in_rr_run_obs n cursor (batch j) o hin, hp⟩
  · exact .inr hlt

/-! ## Structural invariance and eventuality over yielding pools

A pool each of whose threads, from every invariant state, closes an exact finite turn and returns
to the same thread satisfies `AG` of any formula holding at all invariant configurations
(`ClosedTurns`); if moreover every turn emits a target observation or decreases a well-founded
rank of ghost data (`RankedTurns`), then `AF` of the target holds. The nondeterministic rules
require this of every selectable slot: no fair selection is assumed. -/

section PoolDefs
variable {E B : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))

/-- Exact (`≅`, here `=`) response relation for thread segments. -/
abbrev exactW : (Y : Type) → ctreeW W B Y → ctreeW W B Y → Prop := fun _ t u => t = u

/-- Every slot closes an exact turn back to itself from every invariant state. -/
def ClosedTurns {G : Type} {n : Nat} (ts : Pool E B (n + 1)) (Inv : G → Sg → Prop) : Prop :=
  ∀ g σ (i : Fin (n + 1)), Inv g σ →
    ∃ g' σ' logs, segment_to handler exactW ts[i] σ logs ts[i] σ' ∧ Inv g' σ'

/-- `ClosedTurns` where each turn emits a `P` observation or decreases `rank` along `ltV`. -/
def RankedTurns {G V : Type} {n : Nat} (ts : Pool E B (n + 1)) (Inv : G → Sg → Prop)
    (rank : G → V) (ltV : V → V → Prop) (P : W → Prop) : Prop :=
  ∀ g σ (i : Fin (n + 1)), Inv g σ →
    ∃ g' σ' logs, segment_to handler exactW ts[i] σ logs ts[i] σ' ∧
      Inv g' σ' ∧ ((∃ o ∈ logs, P o) ∨ ltV (rank g') (rank g))

theorem ranked_turns_closed {G V : Type} {n : Nat} (ts : Pool E B (n + 1))
    (Inv : G → Sg → Prop) (rank : G → V) (ltV : V → V → Prop) (P : W → Prop) :
    RankedTurns handler ts Inv rank ltV P → ClosedTurns handler ts Inv :=
  fun hr g σ i hinv =>
    let ⟨g', σ', logs, hseg, hinv', _⟩ := hr g σ i hinv
    ⟨g', σ', logs, hseg, hinv'⟩

theorem ranked_turns_mono {G V : Type} {n : Nat} (ts : Pool E B (n + 1))
    (Inv : G → Sg → Prop) (rank : G → V) (ltV : V → V → Prop) (P Q : W → Prop) :
    (∀ o, P o → Q o) → RankedTurns handler ts Inv rank ltV P →
      RankedTurns handler ts Inv rank ltV Q :=
  fun hPQ hr g σ i hinv =>
    let ⟨g', σ', logs, hseg, hinv', hcase⟩ := hr g σ i hinv
    ⟨g', σ', logs, hseg, hinv', hcase.imp (fun ⟨o, hin, hp⟩ => ⟨o, hin, hPQ o hp⟩) id⟩

end PoolDefs

/-- A formula closed under prefixing a log holds on every log prefix of a tree it holds on. -/
private theorem prefix_logs {W W' : Type} {B : Effect.{0}} {X : Type} (inj : W → W')
    (φ : TiclL (writerE W'))
    (hlog : ∀ (o : W) (t : ctreeW W' B X) w, NotDone w →
      entails φ t (.obs (E := writerE W') (inj o) ⟨⟩) →
      entails φ (CTree.vis (E := writerE W') (inj o) fun _ => t) w)
    (xs : List W) (t : ctreeW W' B X) (ht : ∀ w, NotDone w → entails φ t w) :
    ∀ w, NotDone w → entails φ (emit_list (xs.map inj) t) w := by
  induction xs with
  | nil => exact ht
  | cons o xs ih =>
    intro w hw
    rw [List.map_cons, emit_list_cons]
    exact hlog o _ w hw (ih _ (.obs _ _))

section PoolRules
variable {E B : Effect.{0}} [Bn -< B] [LawfulSubeffect Bn B] {W Sg : Type}
  (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))

theorem ag_pool_nd_invariance {G : Type} {n : Nat} (ts : Pool E B (n + 1)) (Inv : G → Sg → Prop)
    (φ : TiclL (writerE W)) :
    ClosedTurns handler ts Inv →
    (∀ (o : W) (t : ctreeW W B (PUnit × Sg)) w, NotDone w →
      entails φ t (.obs (E := writerE W) o ⟨⟩) →
      entails φ (CTree.vis (E := writerE W) o fun _ => t) w) →
    (∀ g σ focus w, Inv g σ → NotDone w →
      entails φ (interp_schedule_nd handler (n + 1) ts focus σ) w) →
    ∀ g σ focus w, Inv g σ → NotDone w →
      entails (AG φ) (interp_schedule_nd handler (n + 1) ts focus σ) w := by
  intro hclosed hlog hφ g σ focus w hinv hw
  let N (σ : Sg) := interp_schedule_nd handler (n + 1) ts none σ
  have hfocus : ∀ g σ i, Inv g σ → ∃ (g' : G) (σ' : Sg) (logs : List W), Inv g' σ' ∧
      interp_schedule_nd handler (n + 1) ts (some i) σ ~ emit_list logs (N σ') :=
    fun g σ i hinv =>
      let ⟨g', σ', logs, hseg, hinv'⟩ := hclosed g σ i hinv
      ⟨g', σ', logs, hinv', segment_pool_nd_loop handler n ts i σ logs σ' hseg⟩
  obtain ⟨g₀, σ₀, logs₀, hinv₀, h₀⟩ : ∃ (g' : G) (σ' : Sg) (logs : List W), Inv g' σ' ∧
      interp_schedule_nd handler (n + 1) ts focus σ ~ emit_list logs (N σ') := by
    cases focus with
    | none => exact ⟨g, σ, [], hinv, sbisim_refl _⟩
    | some i => exact hfocus g σ i hinv
  refine coinduction (b := agcF (entails φ))
    (ι := {p : ctreeW W B (PUnit × Sg) × World (writerE W) //
      NotDone p.2 ∧ ∃ (g : G) (σ : Sg) (logs : List W), Inv g σ ∧ p.1 ~ emit_list logs (N σ)})
    (fun p => p.1.1) (fun p => p.1.2) ?_ ⟨(_, w), hw, g₀, σ₀, logs₀, hinv₀, h₀⟩
  rintro R - cih ⟨⟨t, v⟩, hv, g, σ, logs, hinv, ht⟩
  have hnow : entails φ (emit_list logs (N σ)) v := by
    simpa using prefix_logs id φ hlog logs (N σ) (fun w hw => hφ g σ none w hinv hw) v hv
  refine ⟨(proper_entails_meq _ ht).2 hnow, ?_⟩
  cases logs with
  | cons o logs =>
    refine ⟨(proper_can_step ht).2 (can_step_log_bind o hv), fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht tr
    simp only [emit_list_cons] at tr
    obtain ⟨_, hw', rfl, -⟩ := ktrans_vis.1 tr
    exact cih ⟨(t', w'), hw' ▸ .obs _ _, g, σ, logs, hinv, hu⟩
  | nil =>
    have ht' := sbisim_trans ht (interp_schedule_nd_select handler n ts σ)
    refine ⟨(proper_can_step ht').2 (can_step_brSn.2 hv), fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht' tr
    obtain ⟨j, rfl, rfl, -⟩ := ktrans_brSn.1 tr
    obtain ⟨g', σ', logs', hinv', hj⟩ := hfocus g σ j hinv
    exact cih ⟨(t', v), hv, g', σ', logs', hinv', sbisim_trans hu hj⟩

theorem aul_pool_nd_eventually {G V : Type} {n : Nat} (ts : Pool E B (n + 1))
    (Inv : G → Sg → Prop) (rank : G → V) (ltV : V → V → Prop) (P : W → Prop) :
    WellFounded ltV → RankedTurns handler ts Inv rank ltV P →
    ∀ g σ focus w, Inv g σ → NotDone w →
      entails (AF (visWₜ P)) (interp_schedule_nd handler (n + 1) ts focus σ) w := by
  intro hwf hranked g
  refine (InvImage.wf rank hwf).induction (C := fun g => ∀ σ focus w, Inv g σ → NotDone w →
    entails (AF (visWₜ P)) (interp_schedule_nd handler (n + 1) ts focus σ) w) g
    fun g ih => ?_
  intro σ focus w hinv hw
  have hsome : ∀ i w, NotDone w →
      entails (AF (visWₜ P)) (interp_schedule_nd handler (n + 1) ts (some i) σ) w := by
    intro i w hw
    obtain ⟨g', σ', logs, hseg, hinv', hcase⟩ := hranked g σ i hinv
    refine (proper_entails_meq _ (segment_pool_nd_loop handler n ts i σ logs σ' hseg)).2 ?_
    rcases hcase with ⟨o, hin, hp⟩ | hlt
    · exact af_emit_list_member logs _ w P o hw hin hp
    · exact af_emit_list logs _ w P hw (ih g' hlt σ' none _ hinv' (after_logs_not_done _ hw))
  cases focus with
  | some i => exact hsome i w hw
  | none =>
    refine (proper_entails_meq _ (interp_schedule_nd_select handler n ts σ)).2 ?_
    exact Auc.stepA (ticll_top hw) (can_step_brSn.2 hw) fun t' w' tr => by
      obtain ⟨j, rfl, rfl, -⟩ := ktrans_brSn.1 tr
      exact hsome j _ hw

end PoolRules

/-! The round-robin runner lives at `Bn`; its observations are the program's under `.inl` and
the scheduling decisions under `.inr`. -/

section PoolRulesRR
variable {E : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem ag_pool_rr_invariance {G : Type} {n : Nat} (ts : Pool E Bn (n + 1))
    (Inv : G → Sg → Prop) (φ : TiclL (writerE (W ⊕ Nat))) :
    ClosedTurns handler ts Inv →
    (∀ (o : W) (t : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) w, NotDone w →
      entails φ t (.obs (E := writerE (W ⊕ Nat)) (.inl o) ⟨⟩) →
      entails φ (CTree.vis (E := writerE (W ⊕ Nat)) (.inl o) fun _ => t) w) →
    (∀ g σ focus cursor w, Inv g σ → NotDone w →
      entails φ (interp_schedule_rr handler (n + 1) ts focus cursor σ) w) →
    ∀ g σ focus cursor w, Inv g σ → NotDone w →
      entails (AG φ) (interp_schedule_rr handler (n + 1) ts focus cursor σ) w := by
  intro hclosed hlog hφ g σ focus cursor w hinv hw
  let N (c : Nat) (σ : Sg) := interp_schedule_rr handler (n + 1) ts none c σ
  have hfocus : ∀ g σ i c, Inv g σ → ∃ (g' : G) (σ' : Sg) (logs : List W), Inv g' σ' ∧
      interp_schedule_rr handler (n + 1) ts (some i) c σ ~ emit_list (logs.map .inl) (N c σ') :=
    fun g σ i c hinv =>
      let ⟨g', σ', logs, hseg, hinv'⟩ := hclosed g σ i hinv
      ⟨g', σ', logs, hinv', segment_pool_rr_loop handler n ts i c σ logs σ' hseg⟩
  obtain ⟨g₀, σ₀, logs₀, hinv₀, h₀⟩ : ∃ (g' : G) (σ' : Sg) (logs : List W), Inv g' σ' ∧
      interp_schedule_rr handler (n + 1) ts focus cursor σ ~
        emit_list (logs.map .inl) (N cursor σ') := by
    cases focus with
    | none => exact ⟨g, σ, [], hinv, sbisim_refl _⟩
    | some i => exact hfocus g σ i cursor hinv
  refine coinduction (b := agcF (entails φ))
    (ι := {p : ctreeW (W ⊕ Nat) Bn (PUnit × Sg) × World (writerE (W ⊕ Nat)) //
      NotDone p.2 ∧ ∃ (g : G) (σ : Sg) (c : Nat) (logs : List W), Inv g σ ∧
        p.1 ~ emit_list (logs.map .inl) (N c σ)})
    (fun p => p.1.1) (fun p => p.1.2) ?_ ⟨(_, w), hw, g₀, σ₀, cursor, logs₀, hinv₀, h₀⟩
  rintro R - cih ⟨⟨t, v⟩, hv, g, σ, c, logs, hinv, ht⟩
  refine ⟨(proper_entails_meq _ ht).2
    (prefix_logs .inl φ hlog logs (N c σ) (fun w hw => hφ g σ none c w hinv hw) v hv), ?_⟩
  cases logs with
  | cons o logs =>
    refine ⟨(proper_can_step ht).2 (can_step_log_bind _ hv), fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht tr
    simp only [List.map_cons, emit_list_cons] at tr
    obtain ⟨_, hw', rfl, -⟩ := ktrans_vis.1 tr
    exact cih ⟨(t', w'), hw' ▸ .obs _ _, g, σ, c, logs, hinv, hu⟩
  | nil =>
    have ht' := sbisim_trans ht (interp_schedule_rr_select handler n ts c σ)
    refine ⟨(proper_can_step ht').2 ((can_step_vis PUnit.unit).2 hv), fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht' tr
    obtain ⟨_, hw', rfl, -⟩ := ktrans_vis.1 tr
    obtain ⟨g', σ', logs', hinv', hj⟩ := hfocus g σ (rr_pick n c) (c + 1) hinv
    exact cih ⟨(t', w'), hw' ▸ .obs _ _, g', σ', c + 1, logs', hinv', sbisim_trans hu hj⟩

theorem aul_pool_rr_eventually {G V : Type} {n : Nat} (ts : Pool E Bn (n + 1))
    (Inv : G → Sg → Prop) (rank : G → V) (ltV : V → V → Prop) (P : W → Prop) :
    WellFounded ltV → RankedTurns handler ts Inv rank ltV P →
    ∀ g σ focus cursor w, Inv g σ → NotDone w →
      entails (AF (visWₜ (fair_obs P)))
        (interp_schedule_rr handler (n + 1) ts focus cursor σ) w := by
  intro hwf hranked g
  refine (InvImage.wf rank hwf).induction (C := fun g => ∀ σ focus cursor w, Inv g σ →
    NotDone w → entails (AF (visWₜ (fair_obs P)))
      (interp_schedule_rr handler (n + 1) ts focus cursor σ) w) g fun g ih => ?_
  intro σ focus cursor w hinv hw
  have hsome : ∀ i c w, NotDone w → entails (AF (visWₜ (fair_obs P)))
      (interp_schedule_rr handler (n + 1) ts (some i) c σ) w := by
    intro i c w hw
    obtain ⟨g', σ', logs, hseg, hinv', hcase⟩ := hranked g σ i hinv
    refine (proper_entails_meq _ (segment_pool_rr_loop handler n ts i c σ logs σ' hseg)).2 ?_
    rcases hcase with ⟨o, hin, hp⟩ | hlt
    · exact af_emit_list_member _ _ w _ (.inl o) hw (List.mem_map.2 ⟨o, hin, rfl⟩) hp
    · exact af_emit_list _ _ w _ hw (ih g' hlt σ' none c _ hinv' (after_logs_not_done _ hw))
  cases focus with
  | some i => exact hsome i cursor w hw
  | none =>
    refine (proper_entails_meq _ (interp_schedule_rr_select handler n ts cursor σ)).2 ?_
    exact (af_vis PUnit.unit).1 (.inr ⟨hw, fun _ => hsome _ _ _ (.obs _ _)⟩)

end PoolRulesRR

/-! ## Exact native-return normal forms for finite returning pools

Finite administrative guards do not select another actor. An unfocused selection costs one
`step` under ND and one logged slot under RR; an already-focused slot costs neither. The handler
state is preserved without invoking the handler. -/

section ReturningPoolsND
variable {E B : Effect.{0}} [Bn -< B] {W Sg : Type}
  (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))

private theorem returning_nd_slot (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) (k : Nat)
    (σ : Sg) :
    interp_schedule_nd handler (n + 1) (ts.set i (guards k (pure ⟨⟩))) (some i) σ ~
      interp_schedule_nd handler n (ts.eraseIdx i) none σ := by
  induction k with
  | zero =>
    refine sbisim_trans (interp_schedule_nd_ret handler n _ i σ (by simp)) ?_
    rw [interp_schedule_nd_equ handler n _ _ none σ (remove_replace_pool_equ ts i _)]
    exact sbisim_refl _
  | succ k ih => exact sbisim_trans (segment_nd_focused_guard handler n ts i _ σ) ih

theorem interp_schedule_nd_returns [LawfulSubeffect Bn B] (n : Nat) (ts : Pool E B n)
    (focus : Option (Fin n)) (σ : Sg) :
    (∀ i : Fin n, ∃ k, ts[i] = guards k (pure ⟨⟩)) →
    interp_schedule_nd handler n ts focus σ ~
      Nat.repeat CTree.step (match focus with | none => n | some _ => n.pred)
        (pure (⟨⟩, σ) : ctreeW W B (PUnit × Sg)) := by
  induction n generalizing σ with
  | zero =>
    intro _
    cases focus with
    | some i => exact i.elim0
    | none => exact interp_schedule_nd_empty handler ts σ
  | succ n ih =>
    intro hslots
    have hfocused : ∀ i, interp_schedule_nd handler (n + 1) ts (some i) σ ~
        Nat.repeat CTree.step n (pure (⟨⟩, σ) : ctreeW W B (PUnit × Sg)) := by
      intro i
      obtain ⟨k, hk⟩ := hslots i
      rw [show ts = ts.set i (guards k (pure ⟨⟩ : Thread E B)) by rw [← hk]; simp]
      exact sbisim_trans (returning_nd_slot handler n ts i k σ) (ih _ none σ
        (vector_remove_pointwise (fun (t _ : Thread E B) => ∃ k, t = guards k (pure ⟨⟩))
          ts ts i fun l _ => hslots l))
    cases focus with
    | some i => exact hfocused i
    | none =>
      refine sbisim_trans (interp_schedule_nd_select handler n ts σ) ?_
      obtain ⟨y, -⟩ := bn_reach (B := B) (n + 1) 0
      exact sb_br_l _ y _ _ fun _ => sb_step (hfocused _)

end ReturningPoolsND

section ReturningPoolsRR
variable {E : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

private theorem returning_rr_slot (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k cursor : Nat) (σ : Sg) :
    interp_schedule_rr handler (n + 1) (ts.set i (guards k (pure ⟨⟩))) (some i) cursor σ ~
      interp_schedule_rr handler n (ts.eraseIdx i) none cursor σ := by
  induction k with
  | zero =>
    refine sbisim_trans (interp_schedule_rr_ret handler n _ i cursor σ (by simp)) ?_
    rw [interp_schedule_rr_equ handler n _ _ none cursor σ (remove_replace_pool_equ ts i _)]
    exact sbisim_refl _
  | succ k ih => exact sbisim_trans (segment_rr_focused_guard handler n ts i _ cursor σ) ih

theorem interp_schedule_rr_returns (n : Nat) (ts : Pool E Bn n) (focus : Option (Fin n))
    (cursor : Nat) (σ : Sg) :
    (∀ i : Fin n, ∃ k, ts[i] = guards k (pure ⟨⟩)) →
    interp_schedule_rr handler n ts focus cursor σ ~
      emit_list ((rr_return_picks (match focus with | none => n | some _ => n.pred) cursor).map
          (Sum.inr : Nat → W ⊕ Nat))
        (pure (⟨⟩, σ) : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) := by
  induction n generalizing cursor σ with
  | zero =>
    intro _
    cases focus with
    | some i => exact i.elim0
    | none => exact interp_schedule_rr_empty handler ts cursor σ
  | succ n ih =>
    intro hslots
    have hfocused : ∀ i c, interp_schedule_rr handler (n + 1) ts (some i) c σ ~
        emit_list ((rr_return_picks n c).map (Sum.inr : Nat → W ⊕ Nat))
          (pure (⟨⟩, σ) : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) := by
      intro i c
      obtain ⟨k, hk⟩ := hslots i
      rw [show ts = ts.set i (guards k (pure ⟨⟩ : Thread E Bn)) by rw [← hk]; simp]
      exact sbisim_trans (returning_rr_slot handler n ts i k c σ) (ih _ none c σ
        (vector_remove_pointwise (fun (t _ : Thread E Bn) => ∃ k, t = guards k (pure ⟨⟩))
          ts ts i fun l _ => hslots l))
    cases focus with
    | some i => exact hfocused i cursor
    | none =>
      refine sbisim_trans (interp_schedule_rr_select handler n ts cursor σ) ?_
      rw [rr_return_picks, List.map_cons, emit_list_cons]
      exact sb_vis _ fun _ => hfocused _ _

end ReturningPoolsRR

-- Not ported: nothing. Rocq's second `Abbreviation exactW` (section `PoolRulesRR`) is the same
-- `exactW` at `B := Bn`.

end Tisl.Yield
