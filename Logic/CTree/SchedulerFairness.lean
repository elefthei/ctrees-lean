/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Observed
public import Logic.CTree.AF
public import Logic.CTree.AG

/-!
# Scheduler fairness of the observed scheduler

Temporal consequences of the observed scheduler `schedule_with_offers`: every live slot is offered
after each scheduling point, conditional on `SchedulerProgress`
(← `CTree/Logic/SchedulerFairness.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction Tisl.Notation
open ITree (Effect)

/-- The world that offers live slot `i`. -/
def offer_live_slot {E : Effect.{0}} (n : Nat) (i : LiveSlot n) : TiclL (scheduler_observedE E) :=
  .now fun w => w = .obs (.inl (.offered (live_slot_ref i))) PUnit.unit

section ObservedScheduler
variable {E B : Effect.{0}}

theorem offer_live_slot_now (n : Nat) (i : LiveSlot n) (t : observed_completed E B) :
    entails (offer_live_slot n i) t (.obs (.inl (.offered (live_slot_ref i))) PUnit.unit) :=
  ⟨rfl, .obs _ _⟩

theorem ktrans_vis_raw_inv_no_eqdep {X : Type} (e : (scheduler_observedE E).I)
    (k : (scheduler_observedE E).O e → CTree (scheduler_observedE E) B X)
    (w : World (scheduler_observedE E)) (t' w') (h : ktrans (CTree.vis e k) w t' w') :
    ∃ v, w' = .obs e v ∧ k v = t' ∧ NotDone w :=
  ktrans_vis.1 h

theorem ktrans_scheduler_vis_inv_no_eqdep {X : Type} (obs : SchedulerObsOp)
    (k : PUnit → CTree (scheduler_observedE E) B X)
    (w : World (scheduler_observedE E)) (t' w')
    (h : ktrans (CTree.vis (E := scheduler_observedE E) (.inl obs) k) w t' w') :
    w' = .obs (.inl obs) PUnit.unit ∧ k ⟨⟩ = t' ∧ NotDone w := by
  obtain ⟨_, rfl, rfl, hd⟩ := ktrans_vis.1 h
  exact ⟨rfl, rfl, hd⟩

theorem offered_in_scheduler_prefix_chain_implies_AF (n : Nat) (i : LiveSlot n)
    (u actual bridge : observed_completed E B) (w : World (scheduler_observedE E))
    (hb : bridge.unfold = actual.unfold) (hc : SchedulerEquChain bridge u) (hnd : NotDone w)
    (hp : OfferedInSchedulerPrefix n i u) :
    entails (AF (offer_live_slot n i)) actual w := by
  induction hp generalizing actual bridge w with
  | here k hobs =>
    obtain ⟨ka, hka, -⟩ := scheduler_equ_chain_scheduler_vis_inv_no_eqdep _ k bridge _ hc hobs
    have ha : actual = CTree.vis (E := scheduler_observedE E) (.inl _) ka :=
      unfold_inj (by rw [← hb, hka, unfold_vis])
    rw [ha]
    exact (af_vis PUnit.unit).1 (.inr ⟨hnd, fun _ => .matchA (offer_live_slot_now n i _)⟩)
  | later obs k hobs _ ih =>
    obtain ⟨ka, hka, hcont⟩ := scheduler_equ_chain_scheduler_vis_inv_no_eqdep _ k bridge _ hc hobs
    have ha : actual = CTree.vis (E := scheduler_observedE E) (.inl _) ka :=
      unfold_inj (by rw [← hb, hka, unfold_vis])
    rw [ha]
    exact (af_vis PUnit.unit).1
      (.inr ⟨hnd, fun _ => ih (ka ⟨⟩) (ka ⟨⟩) _ rfl hcont (.obs _ _)⟩)

theorem offered_in_scheduler_prefix_implies_AF (n : Nat) (i : LiveSlot n)
    (t : observed_completed E B) (w : World (scheduler_observedE E)) (hnd : NotDone w)
    (hp : OfferedInSchedulerPrefix n i t) : entails (AF (offer_live_slot n i)) t w :=
  offered_in_scheduler_prefix_chain_implies_AF n i t t t w rfl (.refl _) hnd hp

/-- At a nonempty scheduling point, every live slot is eventually offered. -/
def scheduling_point_offer_obligation (t : observed_completed E B)
    (w : World (scheduler_observedE E)) : Prop :=
  ∀ n, w = .obs (.inl (.point (n + 1))) PUnit.unit →
    ∀ i : LiveSlot (n + 1), entails (AF (offer_live_slot (n + 1) i)) t w

/-- Worlds that are not a nonempty scheduling point. -/
def non_scheduling_point_world : World (scheduler_observedE E) → Prop
  | .obs (.inl (.point (_ + 1))) _ => False
  | _ => True

/-- The world side of a labelled transition, as `ktrans` fixes it. -/
def label_world : Label (scheduler_observedE E) → World (scheduler_observedE E) →
    World (scheduler_observedE E) → Prop
  | .tau, w, w' => NotDone w ∧ w' = w
  | .obs e x, w, w' => NotDone w ∧ w' = .obs e x
  | .val _, _, w' => IsDone PUnit w'

theorem ktrans_label_world {t t' : observed_completed E B} {w w'} (h : ktrans t w t' w') :
    ∃ l, trans l t t' ∧ label_world l w w' := by
  obtain ⟨l, tr, h⟩ := ktrans_trans.1 h
  refine ⟨l, tr, ?_⟩
  rcases h with ⟨rfl, hd, rfl⟩ | ⟨e, x, rfl, hd, rfl⟩ | ⟨x, rfl, -, -, rfl⟩ |
    ⟨e, v, x, rfl, -, -, rfl⟩
  · exact ⟨hd, rfl⟩
  · exact ⟨hd, rfl⟩
  · exact .done x
  · exact .finish e v x

/-- The functor of `SchedulerProgress`: the tree can step, and so can every successor. -/
def schedulerProgressF :
    Mon (Rel (observed_completed E B) (World (scheduler_observedE E))) where
  body R t w := can_step t w ∧ ∀ t' w', ktrans t w t' w' → R t' w'
  mono h _ _ H := ⟨H.1, fun t' w' tr => h _ _ (H.2 t' w' tr)⟩

/-- The observed scheduler never gets stuck or terminates (Rocq coinductive `SchedulerProgress`). -/
def SchedulerProgress : observed_completed E B → World (scheduler_observedE E) → Prop :=
  gfp schedulerProgressF

theorem scheduler_progress_unfold {t : observed_completed E B} {w} :
    SchedulerProgress t w ↔ can_step t w ∧ ∀ t' w', ktrans t w t' w' → SchedulerProgress t' w' :=
  ⟨fun h => gfp_pfp (b := schedulerProgressF) t w h,
   fun h => b_chain (gfp_chain schedulerProgressF) t w h⟩

variable [Bn -< B]

theorem show_no_focus_offers_every_live_slot (n : Nat) (v : Pool E B (n + 1))
    (i : LiveSlot (n + 1)) :
    entails (AF (offer_live_slot (n + 1) i)) (schedule_with_offers (n + 1) v none) .pure :=
  offered_in_scheduler_prefix_implies_AF _ _ _ _ .pure
    (show_no_focus_offers_every_live_slot_prefix n v i)

theorem no_focus_offers_every_live_slot (n : Nat) (v : Pool E B (n + 1))
    (i : LiveSlot (n + 1)) :
    entails (AF (offer_live_slot (n + 1) i)) (schedule_with_offers (n + 1) v none) .pure :=
  show_no_focus_offers_every_live_slot n v i

/-- The canonical shapes reachable from `schedule_with_offers` (Rocq `SchedulerOfferCanonical`):
the scheduler, its offer prefix, the hidden choice and the picked slot, plus terminal worlds. -/
inductive SchedulerOfferCanonical : observed_completed E B → World (scheduler_observedE E) → Prop
  | schedule (n : Nat) (v : Pool E B n) (focus : Option (Fin n)) (w) :
      non_scheduling_point_world w → SchedulerOfferCanonical (schedule_with_offers n v focus) w
  | prefix_at_point (n : Nat) (v : Pool E B (n + 1)) :
      SchedulerOfferCanonical (schedule_with_offers_offer_prefix (n + 1) (n + 1) (fun i => i) v)
        (.obs (.inl (.point (n + 1))) PUnit.unit)
  | prefix_elsewhere (m r : Nat) (embed : LiveSlot r → LiveSlot m) (v : Pool E B m) (w) :
      non_scheduling_point_world w →
      SchedulerOfferCanonical (schedule_with_offers_offer_prefix m r embed v) w
  | choice (n : Nat) (v : Pool E B (n + 2)) (w) : non_scheduling_point_world w →
      SchedulerOfferCanonical (CTree.brn (n + 2) fun i =>
        .vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (n + 2) v (some i)) w
  | picked (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) (w) :
      non_scheduling_point_world w →
      SchedulerOfferCanonical
        (.vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (n + 1) v (some i)) w
  | done (t) (x : PUnit) : SchedulerOfferCanonical t (.done x)
  | finish (t) (e : (scheduler_observedE E).I) (v : (scheduler_observedE E).O e) (x : PUnit) :
      SchedulerOfferCanonical t (.finish e v x)

theorem scheduler_offer_canonical_obligation {t : observed_completed E B}
    {w : World (scheduler_observedE E)} (hc : SchedulerOfferCanonical t w) :
    scheduling_point_offer_obligation t w := by
  intro k hk i
  cases hc with
  | prefix_at_point n v =>
    have : n = k := by
      injection hk with h1 h2; injection h1 with h1; injection h1 with h1; omega
    subst this
    exact offered_in_scheduler_prefix_implies_AF _ _ _ _ (.obs _ _)
      (schedule_with_offers_offer_prefix_offers (n + 1) (n + 1) (fun j => j) v i)
  | done | finish => cases hk
  | _ => subst hk; contradiction

/-- What every head of a canonical tree steps to (one node, before `trans` crawls guards and
hidden branches). -/
def canonicalHead (w : World (scheduler_observedE E)) :
    CTreeF (scheduler_observedE E) B PUnit (observed_completed E B) → Prop
  | .ret _ | .stuck => True
  | .guard t | .step t => SchedulerOfferCanonical t w
  | .br _ k => ∀ x, SchedulerOfferCanonical (k x) w
  | .vis e k => ∀ x, SchedulerOfferCanonical (k x) (.obs e x)

theorem canonical_head {t : observed_completed E B} {w} (hc : SchedulerOfferCanonical t w)
    (hnd : NotDone w) : canonicalHead w t.unfold := by
  cases hc with
  | schedule n v focus w hw =>
    cases focus with
    | none =>
      cases n with
      | zero => rw [schedule_with_offers_empty_none]; trivial
      | succ n => rw [schedule_with_offers_no_focus_nonempty]; exact fun _ => .prefix_at_point n v
    | some i =>
      cases n with
      | zero => exact i.elim0
      | succ n =>
        cases hv : v[i].unfold with
        | ret x => rw [schedule_with_offers_focused_ret n v i hv]; exact .schedule _ _ _ _ hw
        | stuck => rw [schedule_with_offers_focused_stuck n v i hv]; trivial
        | step t0 => rw [schedule_with_offers_focused_step n v i t0 hv]; exact .schedule _ _ _ _ hw
        | guard t0 =>
          rw [schedule_with_offers_focused_guard n v i t0 hv]; exact .schedule _ _ _ _ hw
        | br c k =>
          rw [schedule_with_offers_focused_br n v i k hv]; exact fun _ => .schedule _ _ _ _ hw
        | vis e k =>
          rcases e with y | f | e
          · rw [schedule_with_offers_focused_yield n v i k hv]; exact .schedule _ _ _ _ hw
          · rw [schedule_with_offers_focused_fork n v i k hv]; exact .schedule _ _ _ _ hw
          · rw [schedule_with_offers_focused_user_event n v i e k hv]
            exact fun _ => .schedule _ _ _ _ trivial
  | prefix_at_point n v =>
    rw [schedule_with_offers_offer_prefix_succ]
    exact fun _ => .prefix_elsewhere _ _ _ _ _ trivial
  | prefix_elsewhere m r embed v w hw =>
    cases r with
    | succ r =>
      rw [schedule_with_offers_offer_prefix_succ]
      exact fun _ => .prefix_elsewhere _ _ _ _ _ trivial
    | zero =>
      cases m with
      | zero => rw [schedule_with_offers_offer_prefix]; trivial
      | succ m =>
        rw [schedule_with_offers_offer_prefix_zero_nonempty]
        cases m with
        | zero => simp only [unfold_vis]; exact fun _ => .schedule _ _ _ _ trivial
        | succ m =>
          simp only [CTree.brn, CTree.br', unfold_br]
          exact fun _ => .picked _ _ _ _ hw
  | choice n v w hw =>
    simp only [CTree.brn, CTree.br', unfold_br]
    exact fun _ => .picked _ _ _ _ hw
  | picked n v i w hw =>
    simp only [unfold_vis]
    exact fun _ => .schedule _ _ _ _ trivial
  | done | finish => cases hnd

theorem canonical_of_isDone {t : observed_completed E B} {w} (h : IsDone PUnit w) :
    SchedulerOfferCanonical t w := by
  cases h with
  | done x => exact .done t x
  | finish e v x => exact .finish t e v x

theorem scheduler_offer_canonical_trans {l : Label (scheduler_observedE E)}
    {os : CTreeF (scheduler_observedE E) B PUnit (observed_completed E B)}
    {t' : observed_completed E B} (tr : Trans_ l os t') :
    ∀ w w', (NotDone w → canonicalHead w os) → label_world l w w' →
      SchedulerOfferCanonical t' w' := by
  induction tr with
  | br x _ ih => exact fun w w' h hlw => ih w w' (fun nd => canonical_head (h nd x) nd) hlw
  | guard _ ih => exact fun w w' h hlw => ih w w' (fun nd => canonical_head (h nd) nd) hlw
  | step => rintro w _ h ⟨nd, rfl⟩; exact h nd
  | obs x => rintro w _ h ⟨nd, rfl⟩; exact h nd x
  | val => exact fun _ _ _ hlw => canonical_of_isDone hlw

theorem scheduler_offer_canonical_step {t t' : observed_completed E B} {w w'}
    (hc : SchedulerOfferCanonical t w) (h : ktrans t w t' w') : SchedulerOfferCanonical t' w' :=
  let ⟨_, tr, hlw⟩ := ktrans_label_world h
  scheduler_offer_canonical_trans tr w w' (canonical_head hc) hlw

theorem scheduler_progress_shape_implies_AG {t : observed_completed E B} {w}
    (hp : SchedulerProgress t w) (hc : SchedulerOfferCanonical t w) :
    agc scheduling_point_offer_obligation t w :=
  le_gfp (b := agcF scheduling_point_offer_obligation)
    (x := fun t w => SchedulerProgress t w ∧ SchedulerOfferCanonical t w)
    (fun _ _ ⟨hp, hc⟩ =>
      have hp := scheduler_progress_unfold.1 hp
      ⟨scheduler_offer_canonical_obligation hc, hp.1,
        fun _ _ tr => ⟨hp.2 _ _ tr, scheduler_offer_canonical_step hc tr⟩⟩)
    t w ⟨hp, hc⟩

/-- Under `SchedulerProgress`, at every nonempty scheduling point every live slot is eventually
offered. -/
theorem every_live_slot_is_eventually_offered_at_scheduling_points (n : Nat) (v : Pool E B n)
    (focus : Option (Fin n)) (hp : SchedulerProgress (schedule_with_offers n v focus) .pure) :
    agc scheduling_point_offer_obligation (schedule_with_offers n v focus) .pure :=
  scheduler_progress_shape_implies_AG hp (.schedule n v focus .pure trivial)

theorem show_every_live_slot_is_eventually_offered_at_scheduling_points (n : Nat)
    (v : Pool E B n) (focus : Option (Fin n))
    (hp : SchedulerProgress (schedule_with_offers n v focus) .pure) :
    agc scheduling_point_offer_obligation (schedule_with_offers n v focus) .pure :=
  every_live_slot_is_eventually_offered_at_scheduling_points n v focus hp

end ObservedScheduler

-- Not ported (Rocq `Local`/`Private` helpers of the closure proof, restructured): Rocq `≅` is `=`,
-- so `SchedulerOfferShape` (`∃ u, t ≅ u ∧ SchedulerOfferCanonical u w`) collapses to
-- `SchedulerOfferCanonical`, and `scheduler_offer_shape_{canonical,equ,observe,schedule,
-- prefix_at_point,prefix_elsewhere,choice,picked,done,finish,obligation,ret_step,step}`,
-- `pure_non_scheduling_point`,
-- `obs_offered_non_scheduling_point`, `obs_non_scheduler_non_scheduling_point` (all `trivial`),
-- `observe_choice_schedule`, `observe_prefix_zero_empty`, `observe_picked_schedule` (`simp`),
-- `label_world_is_done` and Ltacs `focused_heads`, `canonical_heads` are replaced by the one-node
-- `canonicalHead`/`canonical_head` and `canonical_of_isDone`.

end Tisl.Yield
