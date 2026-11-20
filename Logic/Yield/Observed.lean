/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Policy
public import Logic.Yield.SBisimAlign
public import Logic.Utils.Utils
public import Logic.Utils.Vectors

/-!
# Scheduler with offer observations

A proof-facing mirror of the nondeterministic scheduler `schedule` that records every unfocused
scheduling point and, at each, the finite set of offered slots, before the native selection.
`forget_scheduler_offers_preserves_schedule` erases this observation tier back to `schedule` up
to strong bisimulation (← `CTree/Interp/Yield/Observed.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Lean.Order Coinduction
open ITree (Effect)

/-- A live slot of a pool of size `n`. -/
abbrev LiveSlot (n : Nat) : Type := Fin n

/-- A live slot together with the pool size it refers to. -/
structure SlotRef : Type where
  slot_pool_size : Nat
  slot_live_slot : LiveSlot slot_pool_size

def live_slot_ref {n : Nat} (i : LiveSlot n) : SlotRef := ⟨n, i⟩

/-- Observation events (Rocq `ObsSchedulingPoint n`, `ObsOffered r`). -/
inductive SchedulerObsOp : Type
  | point (n : Nat)
  | offered (r : SlotRef)

/-- Scheduler observations; every observation answers `PUnit`. -/
@[implicit_reducible] def SchedulerObs : Effect.{0} := ⟨SchedulerObsOp, fun _ => PUnit⟩
unif_hint (x : SchedulerObs.I) where |- SchedulerObs.O x ≟ PUnit

abbrev schedulerObsE : Effect.{0} := SchedulerObs

abbrev scheduler_observedE (E : Effect.{0}) : Effect.{0} := schedulerObsE ⊕ₑ (E ⊕ₑ schedE)

abbrev observed_completed (E B : Effect.{0}) := CTree (scheduler_observedE E) B PUnit

section ObservedSchedulerDef
variable {E B : Effect.{0}}

@[partial_fixpoint_monotone]
theorem brn_mono [Bn -< B] {F : Effect.{0}} {X : Type} α [PartialOrder α] (m : Nat)
    (f : α → Fin m → CTree F B X) : monotone f → monotone (fun x => CTree.brn m (f x)) :=
  fun hf => br'_mono α (B₁ := Bn) ⟨m⟩ (fun a x => f a x.down) fun a b h _ => hf a b h _

mutual
/-- The observed scheduler: an unfocused nonempty pool first emits a scheduling point, then offers
every slot in order (`schedule_with_offers_offer_prefix`), then selects as `schedule` does: a
singleton pool directly, larger pools by a hidden branch. Focused clauses mirror `schedule`. -/
def schedule_with_offers [Bn -< B] :
    (n : Nat) → Pool E B n → Option (Fin n) → observed_completed E B
  | 0, _, none => pure ⟨⟩
  | n + 1, v, none =>
    .vis (.inl (.point (n + 1))) fun _ =>
      schedule_with_offers_offer_prefix (n + 1) (n + 1) (fun i => i) v
  | 0, _, some i => i.elim0
  | n + 1, v, some i =>
    match v[i].unfold with
    | .ret _ => .guard (schedule_with_offers n (v.eraseIdx i) none)
    | .stuck => .stuck
    | .br c k => .br c fun j => schedule_with_offers (n + 1) (v.set i (k j)) (some i)
    | .step t => .step (schedule_with_offers (n + 1) (v.set i t) (some i))
    | .guard t => .guard (schedule_with_offers (n + 1) (v.set i t) (some i))
    | .vis (.inl _) k => .guard (schedule_with_offers (n + 1) (v.set i (k ⟨⟩)) none)
    | .vis (.inr (.inl _)) k =>
      .guard (schedule_with_offers (n + 2) (Vector.cons (k true) (v.set i (k false)))
        (some i.succ))
    | .vis (.inr (.inr e)) k =>
      .vis (.inr (.inl e)) fun x => schedule_with_offers (n + 1) (v.set i (k x)) (some i)
partial_fixpoint

/-- Offer the `remaining` slots `embed 0, embed 1, …`, then select. -/
def schedule_with_offers_offer_prefix [Bn -< B] :
    (pool_size remaining : Nat) → (LiveSlot remaining → LiveSlot pool_size) →
      Pool E B pool_size → observed_completed E B
  | 0, 0, _, _ => pure ⟨⟩
  | 1, 0, _, v => .vis (.inr (.inr (0 : Nat))) fun _ => schedule_with_offers 1 v (some 0)
  | n + 2, 0, _, v =>
    CTree.brn (n + 2) fun i =>
      .vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (n + 2) v (some i)
  | m, r + 1, embed, v =>
    .vis (.inl (.offered (live_slot_ref (embed 0)))) fun _ =>
      schedule_with_offers_offer_prefix m r (fun i => embed i.succ) v
partial_fixpoint
end

end ObservedSchedulerDef

/-- Erase the observation tier: observations answer `⟨⟩`, other events are re-triggered. -/
def handle_scheduler_offers {E B : Effect.{0}} :
    (e : (scheduler_observedE E).I) → CTree (E ⊕ₑ schedE) B ((scheduler_observedE E).O e)
  | .inl _ => pure ⟨⟩
  | .inr e => CTree.trigger e

def forget_scheduler_offers {E B : Effect.{0}} {X : Type} (t : CTree (scheduler_observedE E) B X) :
    CTree (E ⊕ₑ schedE) B X :=
  interp handle_scheduler_offers t

@[simp] theorem forget_scheduler_offers_obs {E B : Effect.{0}} {X : Type} (o : SchedulerObsOp)
    (k : PUnit → CTree (scheduler_observedE E) B X) :
    forget_scheduler_offers (.vis (.inl o) k) = .guard (forget_scheduler_offers (k ⟨⟩)) := by
  simp [forget_scheduler_offers, handle_scheduler_offers]

@[simp] theorem forget_scheduler_offers_event {E B : Effect.{0}} {X : Type}
    (e : (E ⊕ₑ schedE).I) (k : (E ⊕ₑ schedE).O e → CTree (scheduler_observedE E) B X) :
    forget_scheduler_offers (.vis (.inr e) k) =
      .vis e fun x => .guard (forget_scheduler_offers (k x)) := by
  simp [forget_scheduler_offers, handle_scheduler_offers, CTree.trigger]

section ObservedScheduler
variable {E B : Effect.{0}} [Bn -< B]

/-! ## One-node facts about the observed scheduler -/

@[simp] theorem schedule_with_offers_empty_none (v : Pool E B 0) :
    (schedule_with_offers 0 v none).unfold = .ret ⟨⟩ := by
  rw [schedule_with_offers]; rfl

theorem schedule_with_offers_no_focus_nonempty (n : Nat) (v : Pool E B (n + 1)) :
    (schedule_with_offers (n + 1) v none).unfold =
      .vis (.inl (.point (n + 1))) fun _ =>
        schedule_with_offers_offer_prefix (n + 1) (n + 1) (fun i => i) v := by
  rw [schedule_with_offers]; rfl

theorem schedule_with_offers_offer_prefix_succ (m n : Nat) (embed : LiveSlot (n + 1) → LiveSlot m)
    (v : Pool E B m) :
    (schedule_with_offers_offer_prefix m (n + 1) embed v).unfold =
      .vis (.inl (.offered (live_slot_ref (embed 0)))) fun _ =>
        schedule_with_offers_offer_prefix m n (fun i => embed i.succ) v := by
  rw [schedule_with_offers_offer_prefix]; rfl

theorem schedule_with_offers_offer_prefix_zero_nonempty (n : Nat)
    (embed : LiveSlot 0 → LiveSlot (n + 1)) (v : Pool E B (n + 1)) :
    (schedule_with_offers_offer_prefix (n + 1) 0 embed v).unfold =
      (match n, v with
        | 0, v => .vis (.inr (.inr (0 : Nat))) fun _ => schedule_with_offers 1 v (some 0)
        | m + 1, v => CTree.brn (m + 2) fun i =>
            .vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (m + 2) v (some i)
        : observed_completed E B).unfold := by
  cases n <;> rw [schedule_with_offers_offer_prefix]

/-- The exhausted offer prefix does not depend on the (empty) embedding. -/
theorem schedule_with_offers_offer_prefix_zero (m : Nat) (embed embed' : LiveSlot 0 → LiveSlot m)
    (v : Pool E B m) :
    schedule_with_offers_offer_prefix m 0 embed v =
      schedule_with_offers_offer_prefix m 0 embed' v := by
  rw [show embed = embed' from funext fun i => i.elim0]

theorem schedule_with_offers_focused_ret (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .ret ⟨⟩) :
    (schedule_with_offers (n + 1) v (some i)).unfold =
      .guard (schedule_with_offers n (v.eraseIdx i) none) := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

theorem schedule_with_offers_focused_stuck (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .stuck) : (schedule_with_offers (n + 1) v (some i)).unfold = .stuck := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

theorem schedule_with_offers_focused_br (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    {c : B.I} (k : B.O c → Thread E B) (h : v[i].unfold = .br c k) :
    (schedule_with_offers (n + 1) v (some i)).unfold =
      .br c fun j => schedule_with_offers (n + 1) (v.set i (k j)) (some i) := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

theorem schedule_with_offers_focused_step (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .step t) :
    (schedule_with_offers (n + 1) v (some i)).unfold =
      .step (schedule_with_offers (n + 1) (v.set i t) (some i)) := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

theorem schedule_with_offers_focused_guard (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .guard t) :
    (schedule_with_offers (n + 1) v (some i)).unfold =
      .guard (schedule_with_offers (n + 1) (v.set i t) (some i)) := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

theorem schedule_with_offers_focused_yield (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E B) (h : v[i].unfold = .vis (.inl ⟨⟩) k) :
    (schedule_with_offers (n + 1) v (some i)).unfold =
      .guard (schedule_with_offers (n + 1) (v.set i (k ⟨⟩)) none) := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

theorem schedule_with_offers_focused_fork (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E B) (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    (schedule_with_offers (n + 1) v (some i)).unfold =
      .guard (schedule_with_offers (n + 2) (Vector.cons (k true) (v.set i (k false)))
        (some i.succ)) := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

theorem schedule_with_offers_focused_user_event (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (e : E.I) (k : E.O e → Thread E B)
    (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    (schedule_with_offers (n + 1) v (some i)).unfold =
      .vis (.inr (.inl e)) fun x => schedule_with_offers (n + 1) (v.set i (k x)) (some i) := by
  conv => lhs; rw [schedule_with_offers]
  rw [h]; rfl

/-! Tree-level forms of the unfocused one-node facts. -/

theorem swo_empty_equ (v : Pool E B 0) : schedule_with_offers 0 v none = .ret ⟨⟩ :=
  observe_equ_go _ _ (schedule_with_offers_empty_none v)

theorem swo_no_focus_equ (n : Nat) (v : Pool E B (n + 1)) :
    schedule_with_offers (n + 1) v none =
      .vis (.inl (.point (n + 1))) fun _ =>
        schedule_with_offers_offer_prefix (n + 1) (n + 1) (fun i => i) v :=
  observe_equ_go _ _ (schedule_with_offers_no_focus_nonempty n v)

theorem swo_prefix_succ_equ (m n : Nat) (embed : LiveSlot (n + 1) → LiveSlot m) (v : Pool E B m) :
    schedule_with_offers_offer_prefix m (n + 1) embed v =
      .vis (.inl (.offered (live_slot_ref (embed 0)))) fun _ =>
        schedule_with_offers_offer_prefix m n (fun i => embed i.succ) v :=
  observe_equ_go _ _ (schedule_with_offers_offer_prefix_succ m n embed v)

theorem swo_prefix_zero_nonempty_equ (n : Nat) (embed : LiveSlot 0 → LiveSlot (n + 1))
    (v : Pool E B (n + 1)) :
    schedule_with_offers_offer_prefix (n + 1) 0 embed v =
      (match n, v with
        | 0, v => .vis (.inr (.inr (0 : Nat))) fun _ => schedule_with_offers 1 v (some 0)
        | m + 1, v => CTree.brn (m + 2) fun i =>
            .vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (m + 2) v (some i)
        : observed_completed E B) :=
  unfold_inj (schedule_with_offers_offer_prefix_zero_nonempty n embed v)

/-! ## Pool congruence -/

/-- Equal pools in the root, offer, choice and selected phases (Rocq `observed_pool_rel`). -/
inductive ObservedPoolRel : observed_completed E B → observed_completed E B → Prop
  | root (n : Nat) (v w : Pool E B n) (focus : Option (Fin n)) :
      pool_equ v w →
      ObservedPoolRel (schedule_with_offers n v focus) (schedule_with_offers n w focus)
  | offer (m r : Nat) (embed : LiveSlot r → LiveSlot m) (v w : Pool E B m) :
      pool_equ v w →
      ObservedPoolRel (schedule_with_offers_offer_prefix m r embed v)
        (schedule_with_offers_offer_prefix m r embed w)
  | choice (n : Nat) (v w : Pool E B (n + 2)) :
      pool_equ v w →
      ObservedPoolRel
        (CTree.brn (n + 2) fun i =>
          .vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (n + 2) v (some i))
        (CTree.brn (n + 2) fun i =>
          .vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (n + 2) w (some i))
  | selected (n : Nat) (v w : Pool E B (n + 1)) (i : Fin (n + 1)) :
      pool_equ v w →
      ObservedPoolRel
        (.vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (n + 1) v (some i))
        (.vis (.inr (.inr (slot_index i))) fun _ => schedule_with_offers (n + 1) w (some i))

theorem schedule_with_offers_pool_proper (n : Nat) (v w : Pool E B n) (focus : Option (Fin n))
    (hvw : pool_equ v w) : schedule_with_offers n v focus = schedule_with_offers n w focus := by
  rw [Vector.ext fun i h => hvw ⟨i, h⟩]

theorem schedule_with_offers_focus_guards (a : Nat) : ∀ (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (x : Thread E B), v[i] = guards a x →
    schedule_with_offers (n + 1) v (some i) =
      guards a (schedule_with_offers (n + 1) (v.set i x) (some i)) := by
  induction a with
  | zero =>
    intro n v i x hx
    subst hx
    exact schedule_with_offers_pool_proper _ _ _ _ fun j => by simp
  | succ a ih =>
    intro n v i x hx
    rw [observe_equ_go _ _ (schedule_with_offers_focused_guard n v i (guards a x)
        (by rw [hx, guards_succ, unfold_guard])),
      ih n (v.set i (guards a x)) i x (by simp)]
    simp

/-! ## Erasure of the observation tier, node by node -/

theorem forget_scheduler_offers_no_focus_nonempty_unfold (n : Nat) (v : Pool E B (n + 1)) :
    forget_scheduler_offers (schedule_with_offers (n + 1) v none) =
      .guard (forget_scheduler_offers
        (schedule_with_offers_offer_prefix (n + 1) (n + 1) (fun i => i) v)) := by
  rw [swo_no_focus_equ, forget_scheduler_offers_obs]

theorem forget_scheduler_offers_offer_prefix_succ_stutter (m n : Nat)
    (embed : LiveSlot (n + 1) → LiveSlot m) (v : Pool E B m) :
    forget_scheduler_offers (schedule_with_offers_offer_prefix m (n + 1) embed v) ~
      forget_scheduler_offers
        (schedule_with_offers_offer_prefix m n (fun i => embed i.succ) v) := by
  rw [swo_prefix_succ_equ, forget_scheduler_offers_obs]
  exact sb_guard _

theorem forget_scheduler_offers_offer_prefix_stutter (m r : Nat) (embed : LiveSlot r → LiveSlot m)
    (v : Pool E B m) :
    forget_scheduler_offers (schedule_with_offers_offer_prefix m r embed v) ~
      forget_scheduler_offers (schedule_with_offers_offer_prefix m 0 (fun i => i.elim0) v) := by
  induction r with
  | zero => rw [schedule_with_offers_offer_prefix_zero m embed]; exact sbisim_refl _
  | succ r ih =>
    exact sbisim_trans (forget_scheduler_offers_offer_prefix_succ_stutter m r embed v) (ih _)

theorem forget_scheduler_offers_no_focus_stutters_to_offer_prefix (n : Nat)
    (v : Pool E B (n + 1)) :
    forget_scheduler_offers (schedule_with_offers (n + 1) v none) ~
      forget_scheduler_offers
        (schedule_with_offers_offer_prefix (n + 1) (n + 1) (fun i => i) v) := by
  rw [forget_scheduler_offers_no_focus_nonempty_unfold]
  exact sb_guard _

/-- Needs `LawfulSubeffect Bn B` (unlike Rocq) to pick the only branch of a unary `brn`. -/
theorem forget_scheduler_offers_offer_prefix_zero_nonempty_unfold [LawfulSubeffect Bn B]
    (n : Nat) (embed : LiveSlot 0 → LiveSlot (n + 1)) (v : Pool E B (n + 1)) :
    forget_scheduler_offers (schedule_with_offers_offer_prefix (n + 1) 0 embed v) ~
      CTree.brn (n + 1) fun i =>
        .vis (.inr (slot_index i)) fun _ =>
          forget_scheduler_offers (schedule_with_offers (n + 1) v (some i)) := by
  rw [swo_prefix_zero_nonempty_equ]
  cases n with
  | zero =>
    obtain ⟨y, -⟩ := LawfulSubeffect.map_surj (E₁ := Bn) (E₂ := B) (⟨1⟩ : ULift Nat)
      (⟨0⟩ : ULift (Fin 1))
    refine sbisim_symm (sb_br_l _ y _ _ fun x => ?_)
    show CTree.vis _ _ ~ _
    rw [fin1_eq (ULift.down _), forget_scheduler_offers_event]
    exact sbisim_vis_id _ _ _ fun _ => ⟨sbisim_symm (sb_guard _), rfl⟩
  | succ n =>
    simp only [forget_scheduler_offers, CTree.brn, CTree.br', interp_br']
    refine sb_br_id _ _ _ fun x => sb_guard_l ?_
    show forget_scheduler_offers (.vis (.inr _) _) ~ _
    rw [forget_scheduler_offers_event]
    exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

theorem forget_scheduler_offers_no_focus_projection_to_focused [LawfulSubeffect Bn B] (n : Nat)
    (v : Pool E B (n + 1)) :
    forget_scheduler_offers (schedule_with_offers (n + 1) v none) ~
      CTree.brn (n + 1) fun i =>
        .vis (.inr (slot_index i)) fun _ =>
          forget_scheduler_offers (schedule_with_offers (n + 1) v (some i)) :=
  sbisim_trans (forget_scheduler_offers_no_focus_stutters_to_offer_prefix n v)
    (sbisim_trans (forget_scheduler_offers_offer_prefix_stutter _ _ _ v)
      (forget_scheduler_offers_offer_prefix_zero_nonempty_unfold n _ v))

theorem forget_scheduler_offers_empty_no_focus_projection (v : Pool E B 0) :
    forget_scheduler_offers (schedule_with_offers 0 v none) ~ (pure ⟨⟩ : Completed E B) := by
  rw [swo_empty_equ]
  show forget_scheduler_offers (pure (PUnit.unit : PUnit)) ~ _
  rw [forget_scheduler_offers, interp_ret]
  exact sbisim_refl _

theorem forget_scheduler_offers_focused_br_projection (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) {c : B.I} (k : B.O c → Thread E B) (h : v[i].unfold = .br c k) :
    forget_scheduler_offers (schedule_with_offers (n + 1) v (some i)) ~
      .br c fun j =>
        forget_scheduler_offers (schedule_with_offers (n + 1) (v.set i (k j)) (some i)) := by
  rw [observe_equ_go _ _ (schedule_with_offers_focused_br n v i k h), fold_br]
  simp only [forget_scheduler_offers, interp_br']
  exact sb_br_id _ _ _ fun _ => sb_guard _

theorem forget_scheduler_offers_focused_step_projection (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (t : Thread E B) (h : v[i].unfold = .step t) :
    forget_scheduler_offers (schedule_with_offers (n + 1) v (some i)) ~
      .step (forget_scheduler_offers (schedule_with_offers (n + 1) (v.set i t) (some i))) := by
  rw [observe_equ_go _ _ (schedule_with_offers_focused_step n v i t h), fold_step]
  simp only [forget_scheduler_offers, interp_step]
  exact sb_step (sb_guard _)

theorem forget_scheduler_offers_focused_fork_projection (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (k : Bool → Thread E B) (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    forget_scheduler_offers (schedule_with_offers (n + 1) v (some i)) ~
      .guard (forget_scheduler_offers (schedule_with_offers (n + 2)
        (Vector.cons (k true) (v.set i (k false))) (some i.succ))) := by
  rw [observe_equ_go _ _ (schedule_with_offers_focused_fork n v i k h), fold_guard]
  simp only [forget_scheduler_offers, interp_guard]
  exact sbisim_refl _

theorem forget_scheduler_offers_focused_user_event_projection (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (e : E.I) (k : E.O e → Thread E B)
    (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    forget_scheduler_offers (schedule_with_offers (n + 1) v (some i)) ~
      .vis (.inl e) fun x =>
        forget_scheduler_offers (schedule_with_offers (n + 1) (v.set i (k x)) (some i)) := by
  rw [observe_equ_go _ _ (schedule_with_offers_focused_user_event n v i e k h), fold_vis,
    forget_scheduler_offers_event]
  exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

/-! ## The erased observed scheduler, node by node -/

/-- The observed scheduler with its observation tier erased. -/
def erased_schedule (n : Nat) (v : Pool E B n) (focus : Option (Fin n)) : Completed E B :=
  forget_scheduler_offers (schedule_with_offers n v focus)

theorem erased_focused_ret_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .ret ⟨⟩) :
    erased_schedule (n + 1) v (some i) = .guard (erased_schedule n (v.eraseIdx i) none) := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_ret n v i h)]
  exact interp_guard _ _

theorem erased_focused_stuck_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .stuck) : erased_schedule (n + 1) v (some i) = .stuck := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_stuck n v i h)]
  exact interp_stuck _

theorem erased_focused_br_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) {c : B.I}
    (k : B.O c → Thread E B) (h : v[i].unfold = .br c k) :
    erased_schedule (n + 1) v (some i) =
      .br c fun j => .guard (erased_schedule (n + 1) (v.set i (k j)) (some i)) := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_br n v i k h)]
  exact interp_br' _ _ _

theorem erased_focused_step_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .step t) :
    erased_schedule (n + 1) v (some i) =
      .step (.guard (erased_schedule (n + 1) (v.set i t) (some i))) := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_step n v i t h)]
  exact interp_step _ _

theorem erased_focused_guard_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .guard t) :
    erased_schedule (n + 1) v (some i) = .guard (erased_schedule (n + 1) (v.set i t) (some i)) := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_guard n v i t h)]
  exact interp_guard _ _

theorem erased_focused_yield_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E B) (h : v[i].unfold = .vis (.inl ⟨⟩) k) :
    erased_schedule (n + 1) v (some i) =
      .guard (erased_schedule (n + 1) (v.set i (k ⟨⟩)) none) := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_yield n v i k h)]
  exact interp_guard _ _

theorem erased_focused_fork_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E B) (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    erased_schedule (n + 1) v (some i) =
      .guard (erased_schedule (n + 2) (Vector.cons (k true) (v.set i (k false)))
        (some i.succ)) := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_fork n v i k h)]
  exact interp_guard _ _

theorem erased_focused_user_event_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E B) (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    erased_schedule (n + 1) v (some i) =
      .vis (.inl e) fun x => .guard (erased_schedule (n + 1) (v.set i (k x)) (some i)) := by
  rw [erased_schedule, observe_equ_go _ _ (schedule_with_offers_focused_user_event n v i e k h)]
  exact forget_scheduler_offers_event _ _

omit [Bn -< B] in
theorem forget_scheduler_offers_guards (a : Nat) (t : observed_completed E B) :
    forget_scheduler_offers (guards a t) = guards a (forget_scheduler_offers t) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [guards_succ, guards_succ, ← ih]; exact interp_guard _ _

theorem erased_focus_guards (a n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) (x : Thread E B)
    (hx : v[i] = guards a x) :
    erased_schedule (n + 1) v (some i) =
      guards a (erased_schedule (n + 1) (v.set i x) (some i)) := by
  rw [erased_schedule, schedule_with_offers_focus_guards a n v i x hx]
  exact forget_scheduler_offers_guards a _

theorem erased_offer_prefix_guards : ∀ (m r : Nat) (embed : LiveSlot r → LiveSlot m)
    (v : Pool E B m),
    forget_scheduler_offers (schedule_with_offers_offer_prefix m r embed v) =
      guards r (forget_scheduler_offers
        (schedule_with_offers_offer_prefix m 0 (fun i => i.elim0) v)) := by
  intro m r
  induction r with
  | zero => intro embed v; rw [schedule_with_offers_offer_prefix_zero m embed]; rfl
  | succ r ih =>
    intro embed v
    rw [swo_prefix_succ_equ, forget_scheduler_offers_obs, ih, guards_succ]

/-- The erased post-offer selection: a singleton pool selects directly, a larger one branches. -/
def erased_pick : (n : Nat) → Pool E B (n + 1) → Completed E B
  | 0, v => .vis (.inr (0 : Nat)) fun _ => .guard (erased_schedule 1 v (some 0))
  | n + 1, v => CTree.brn (n + 2) fun i =>
      .guard (.vis (.inr (slot_index i)) fun _ => .guard (erased_schedule (n + 2) v (some i)))

theorem erased_prefix_zero_equ (n : Nat) (embed : LiveSlot 0 → LiveSlot (n + 1))
    (v : Pool E B (n + 1)) :
    forget_scheduler_offers (schedule_with_offers_offer_prefix (n + 1) 0 embed v) =
      erased_pick n v := by
  rw [swo_prefix_zero_nonempty_equ]
  cases n with
  | zero => exact forget_scheduler_offers_event _ _
  | succ n =>
    simp only [forget_scheduler_offers, CTree.brn, CTree.br', interp_br']
    exact congrArg (CTree.br _)
      (funext fun _ => congrArg CTree.guard (forget_scheduler_offers_event _ _))

theorem erased_no_focus_guards (n : Nat) (v : Pool E B (n + 1)) :
    erased_schedule (n + 1) v none = guards (n + 2) (erased_pick n v) := by
  rw [erased_schedule, forget_scheduler_offers_no_focus_nonempty_unfold, erased_offer_prefix_guards,
    erased_prefix_zero_equ, guards_succ (n + 1)]

/-! ## The erased observed scheduler is guard-aligned with `schedule` -/

/-- Proof relation for the alignment (Rocq `erased_offers_rel`): guard-equivalent pools at a
scheduler root, inside the offer prefix, at the hidden selection, or after the selection event,
each behind finitely many guards. Both focused slots are normalized together. -/
inductive ErasedOffersRel : Completed E B → Completed E B → Prop
  | node (a b n : Nat) (ts us : Pool E B n) (focus : Option (Fin n)) {T U : Completed E B} :
      pool_guard_equ ts us → T = guards a (erased_schedule n ts focus) →
      U = guards b (schedule n us focus) → ErasedOffersRel T U
  | offer (a b n r : Nat) (embed : LiveSlot r → LiveSlot (n + 1)) (ts us : Pool E B (n + 1))
      {T U : Completed E B} : pool_guard_equ ts us →
      T = guards a (forget_scheduler_offers
        (schedule_with_offers_offer_prefix (n + 1) r embed ts)) →
      U = guards b (schedule (n + 1) us none) → ErasedOffersRel T U
  | choice (a b n : Nat) (ts us : Pool E B (n + 2)) {T U : Completed E B} :
      pool_guard_equ ts us → T = guards a (erased_pick (n + 1) ts) →
      U = guards b (CTree.brn (n + 2) fun i =>
        .vis (.inr (slot_index i)) fun _ => schedule (n + 2) us (some i) : Completed E B) →
      ErasedOffersRel T U
  | selected (a b n : Nat) (ts us : Pool E B (n + 1)) (i : Fin (n + 1)) {T U : Completed E B} :
      pool_guard_equ ts us →
      T = guards a (.vis (.inr (slot_index i)) fun _ =>
        .guard (erased_schedule (n + 1) ts (some i)) : Completed E B) →
      U = guards b (.vis (.inr (slot_index i)) fun _ =>
        schedule (n + 1) us (some i) : Completed E B) →
      ErasedOffersRel T U

theorem erased_pick_step (a b n : Nat) (ts us : Pool E B (n + 1)) {T U : Completed E B}
    (hp : pool_guard_equ ts us) (hT : T = guards a (erased_pick n ts))
    (hU : U = guards b (schedule (n + 1) us none)) : GalignF ErasedOffersRel T U := by
  rw [schedule_no_focus_nonempty] at hU
  cases n with
  | zero => exact .vis a b _ _ _ hT hU fun _ => .node 1 0 1 ts us (some 0) hp rfl rfl
  | succ n => exact .br a b _ _ _ hT hU fun _ => .selected 1 0 (n + 1) ts us _ hp rfl rfl

theorem erased_offers_rel_step (T U : Completed E B) (hr : ErasedOffersRel T U) :
    GalignF ErasedOffersRel T U := by
  match hr with
  | .offer a b n r embed ts us hp hT hU =>
    exact erased_pick_step (a + r) b n ts us hp
      (by rw [hT, erased_offer_prefix_guards, erased_prefix_zero_equ, ← guards_add]) hU
  | .choice a b n ts us hp hT hU =>
    exact .br a b _ _ _ hT hU fun _ => .selected 1 0 (n + 1) ts us _ hp rfl rfl
  | .selected a b n ts us i hp hT hU =>
    exact .vis a b _ _ _ hT hU fun _ => .node 1 0 (n + 1) ts us (some i) hp rfl rfl
  | .node a b 0 ts us none hp hT hU =>
    exact .ret a b ⟨⟩
      (by rw [hT, erased_schedule, swo_empty_equ]; exact congrArg (guards a) (interp_ret _ _))
      (by rw [hU]; exact congrArg (guards b) (schedule_policy_empty_equ nd_scheduler us ⟨⟩))
  | .node a b (n + 1) ts us none hp hT hU =>
    exact erased_pick_step (a + (n + 2)) b n ts us hp
      (by rw [hT, erased_no_focus_guards, ← guards_add]) hU
  | .node a b 0 ts us (some i) hp hT hU => exact i.elim0
  | .node a b (N + 1) ts us (some i) hp hT hU =>
    obtain ⟨p, q, x, Ex, Ey⟩ := guard_equ_guards _ _ (hp i)
    have hp' := pool_guard_equ_replace ts us i x hp
    have ET : T = guards (a + p) (erased_schedule (N + 1) (ts.set i x) (some i)) := by
      rw [hT, erased_focus_guards p N ts i x Ex, guards_add]
    have EU : U = guards (b + q) (schedule (N + 1) (us.set i x) (some i)) := by
      rw [hU, schedule_focus_guards q N us i x Ey, guards_add]
    have Hts : (ts.set i x)[i].unfold = x.unfold := by simp
    have Hus : (us.set i x)[i].unfold = x.unfold := by simp
    generalize ts.set i x = ts' at ET hp' Hts
    generalize us.set i x = us' at EU hp' Hus
    clear hT hU
    cases hx : x.unfold with
    | ret r =>
      rw [hx] at Hts Hus
      exact .guard (a + p) (b + q) (erased_schedule N (ts'.eraseIdx i) none)
        (schedule N (us'.eraseIdx i) none)
        (by rw [ET, erased_focused_ret_equ N ts' i Hts, guards_guard])
        (by rw [EU, observe_equ_go _ _ (schedule_focused_ret N us' i Hus), fold_guard,
          guards_guard])
        (.node 0 0 N _ _ none (pool_guard_equ_remove ts' us' i hp') rfl rfl)
    | stuck =>
      rw [hx] at Hts Hus
      exact .stuck (a + p) (b + q) (by rw [ET, erased_focused_stuck_equ N ts' i Hts])
        (by rw [EU, observe_equ_go _ _ (schedule_focused_stuck N us' i Hus)]; rfl)
    | step t =>
      rw [hx] at Hts Hus
      exact .step (a + p) (b + q) (.guard (erased_schedule (N + 1) (ts'.set i t) (some i)))
        (schedule (N + 1) (us'.set i t) (some i))
        (by rw [ET, erased_focused_step_equ N ts' i t Hts])
        (by rw [EU, observe_equ_go _ _ (schedule_focused_step N us' i t Hus)]; rfl)
        (.node 1 0 (N + 1) _ _ (some i) (pool_guard_equ_replace _ _ i t hp') rfl rfl)
    | guard t =>
      rw [hx] at Hts Hus
      exact .guard (a + p) (b + q) (erased_schedule (N + 1) (ts'.set i t) (some i))
        (schedule (N + 1) (us'.set i t) (some i))
        (by rw [ET, erased_focused_guard_equ N ts' i t Hts, guards_guard])
        (by rw [EU, observe_equ_go _ _ (schedule_focused_guard N us' i t Hus), fold_guard,
          guards_guard])
        (.node 0 0 (N + 1) _ _ (some i) (pool_guard_equ_replace _ _ i t hp') rfl rfl)
    | vis e k =>
      rw [hx] at Hts Hus
      rcases e with ⟨⟩ | ⟨⟩ | e
      · exact .guard (a + p) (b + q) (erased_schedule (N + 1) (ts'.set i (k ⟨⟩)) none)
          (schedule (N + 1) (us'.set i (k ⟨⟩)) none)
          (by rw [ET, erased_focused_yield_equ N ts' i k Hts, guards_guard])
          (by rw [EU, observe_equ_go _ _ (schedule_focused_yield N us' i k Hus), fold_guard,
            guards_guard])
          (.node 0 0 (N + 1) _ _ none (pool_guard_equ_replace _ _ i _ hp') rfl rfl)
      · exact .guard (a + p) (b + q)
          (erased_schedule (N + 2) (Vector.cons (k true) (ts'.set i (k false))) (some i.succ))
          (schedule (N + 2) (Vector.cons (k true) (us'.set i (k false))) (some i.succ))
          (by rw [ET, erased_focused_fork_equ N ts' i k Hts, guards_guard])
          (by rw [EU, observe_equ_go _ _ (schedule_focused_fork N us' i k Hus), fold_guard,
            guards_guard])
          (.node 0 0 (N + 2) _ _ (some i.succ)
            (pool_guard_equ_cons _ _ _ (pool_guard_equ_replace _ _ i _ hp')) rfl rfl)
      · exact .vis (a + p) (b + q) (.inl e)
          (fun z => .guard (erased_schedule (N + 1) (ts'.set i (k z)) (some i)))
          (fun z => schedule (N + 1) (us'.set i (k z)) (some i))
          (by rw [ET, erased_focused_user_event_equ N ts' i e k Hts])
          (by rw [EU, observe_equ_go _ _ (schedule_focused_user_event N us' i e k Hus)]; rfl)
          fun _ => .node 1 0 (N + 1) _ _ (some i) (pool_guard_equ_replace _ _ i _ hp') rfl rfl
    | br c k =>
      rw [hx] at Hts Hus
      exact .br (a + p) (b + q) c
        (fun j => .guard (erased_schedule (N + 1) (ts'.set i (k j)) (some i)))
        (fun j => schedule (N + 1) (us'.set i (k j)) (some i))
        (by rw [ET, erased_focused_br_equ N ts' i k Hts])
        (by rw [EU, observe_equ_go _ _ (schedule_focused_br N us' i k Hus)]; rfl)
        fun _ => .node 1 0 (N + 1) _ _ (some i) (pool_guard_equ_replace _ _ i _ hp') rfl rfl

theorem forget_scheduler_offers_schedule_galigned (n : Nat) (ts us : Pool E B n)
    (focus : Option (Fin n)) (hp : pool_guard_equ ts us) :
    galigned (forget_scheduler_offers (schedule_with_offers n ts focus)) (schedule n us focus) :=
  galigned_coind ErasedOffersRel erased_offers_rel_step _ _ (.node 0 0 n ts us focus hp rfl rfl)

theorem forget_scheduler_offers_offer_prefix_galigned (n r : Nat)
    (embed : LiveSlot r → LiveSlot (n + 1)) (ts us : Pool E B (n + 1)) (hp : pool_guard_equ ts us) :
    galigned (forget_scheduler_offers (schedule_with_offers_offer_prefix (n + 1) r embed ts))
      (schedule (n + 1) us none) :=
  galigned_coind ErasedOffersRel erased_offers_rel_step _ _
    (.offer 0 0 n r embed ts us hp rfl rfl)

/-- Erasing the observation tier gives back the native nondeterministic scheduler. -/
theorem forget_scheduler_offers_preserves_schedule (n : Nat) (v : Pool E B n)
    (focus : Option (Fin n)) :
    forget_scheduler_offers (schedule_with_offers n v focus) ~ schedule n v focus :=
  galigned_sbisim _ _ (forget_scheduler_offers_schedule_galigned n v v focus fun _ => .refl _)

end ObservedScheduler

/-! ## Every live slot is offered at a no-focus scheduling point -/

section OfferedPrefix
variable {E B : Effect.{0}}

/-- `i` is offered within the finite prefix of scheduler observations of a tree (Rocq
`offered_in_scheduler_prefix`). -/
inductive OfferedInSchedulerPrefix (n : Nat) (i : LiveSlot n) : observed_completed E B → Prop
  | here {t : observed_completed E B} (k : PUnit → observed_completed E B) :
      t.unfold = .vis (.inl (.offered (live_slot_ref i))) k → OfferedInSchedulerPrefix n i t
  | later {t : observed_completed E B} (obs : SchedulerObsOp) (k : PUnit → observed_completed E B) :
      t.unfold = .vis (.inl obs) k → OfferedInSchedulerPrefix n i (k ⟨⟩) →
      OfferedInSchedulerPrefix n i t

theorem schedule_with_offers_offer_prefix_offers [Bn -< B] (m : Nat) : ∀ (n : Nat)
    (embed : LiveSlot n → LiveSlot m) (v : Pool E B m) (i : LiveSlot n),
    OfferedInSchedulerPrefix m (embed i) (schedule_with_offers_offer_prefix m n embed v) := by
  intro n
  induction n with
  | zero => intro _ _ i; exact i.elim0
  | succ n ih =>
    intro embed v i
    cases i using Fin.cases with
    | zero => exact .here _ (schedule_with_offers_offer_prefix_succ m n embed v)
    | succ j =>
      exact .later _ _ (schedule_with_offers_offer_prefix_succ m n embed v)
        (ih (fun j => embed j.succ) v j)

theorem observed_equ_refl_no_eqdep (t : observed_completed E B) : t = t := rfl

theorem observed_equ_step_no_eqdep (t u : observed_completed E B) (h : t = u) :
    EqF (· = ·) t.unfold u.unfold :=
  h ▸ EqF.refl (fun _ => rfl) _

/-- A scheduler-observation node on the right is matched on the left with equal continuations. -/
def equF_scheduler_vis_result
    (p q : CTreeF (scheduler_observedE E) B PUnit (observed_completed E B)) : Prop :=
  match q with
  | .vis (.inl o) k_right => ∃ k_left, p = .vis (.inl o) k_left ∧ ∀ y, k_left y = k_right y
  | _ => True

theorem equF_scheduler_vis_inv_no_eqdep
    (p q : CTreeF (scheduler_observedE E) B PUnit (observed_completed E B))
    (h : EqF (· = ·) p q) : equF_scheduler_vis_result p q := by
  cases h with
  | vis e hk =>
    rcases e with o | e
    · exact ⟨_, rfl, hk⟩
    · trivial
  | _ => trivial

theorem equ_scheduler_vis_inv_from_observe_no_eqdep (obs : SchedulerObsOp)
    (k : PUnit → observed_completed E B) (t u : observed_completed E B) (htu : t = u)
    (hu : u.unfold = .vis (.inl obs) k) :
    ∃ k_t : PUnit → observed_completed E B, t.unfold = .vis (.inl obs) k_t ∧ k_t ⟨⟩ = k ⟨⟩ := by
  have h := equF_scheduler_vis_inv_no_eqdep _ _ (observed_equ_step_no_eqdep t u htu)
  rw [hu] at h
  obtain ⟨k_t, ht, hk⟩ := h
  exact ⟨k_t, ht, hk ⟨⟩⟩

/-- A finite chain of structural equalities. -/
inductive SchedulerEquChain : observed_completed E B → observed_completed E B → Prop
  | refl (t : observed_completed E B) : SchedulerEquChain t t
  | cons (t u v : observed_completed E B) : t = u → SchedulerEquChain u v → SchedulerEquChain t v

theorem scheduler_equ_chain_scheduler_vis_inv_no_eqdep (obs : SchedulerObsOp)
    (k : PUnit → observed_completed E B) (t u : observed_completed E B)
    (hc : SchedulerEquChain t u) (hobs : u.unfold = .vis (.inl obs) k) :
    ∃ k_t : PUnit → observed_completed E B,
      t.unfold = .vis (.inl obs) k_t ∧ SchedulerEquChain (k_t ⟨⟩) (k ⟨⟩) := by
  induction hc with
  | refl => exact ⟨k, hobs, .refl _⟩
  | cons t mid _ htm _ ih =>
    obtain ⟨k_mid, hmid, hcont⟩ := ih hobs
    obtain ⟨k_t, ht, hstep⟩ := equ_scheduler_vis_inv_from_observe_no_eqdep obs k_mid t mid htm hmid
    exact ⟨k_t, ht, .cons _ _ _ hstep hcont⟩

theorem show_no_focus_offers_every_live_slot_prefix [Bn -< B] (n : Nat) (v : Pool E B (n + 1))
    (i : LiveSlot (n + 1)) :
    OfferedInSchedulerPrefix (n + 1) i (schedule_with_offers (n + 1) v none) :=
  .later _ _ (schedule_with_offers_no_focus_nonempty n v)
    (schedule_with_offers_offer_prefix_offers (n + 1) (n + 1) (fun i => i) v i)

end OfferedPrefix

-- Not ported: `forget_scheduler_offers_equ` (`Proper` instance for `equ`, i.e. `congrArg`);
-- `observed_pool_rel_step` (only used for `schedule_with_offers_pool_proper`, which is proved
-- directly from `Vector.ext`); Ltacs `solve_focused_schedule_with_offers`, `node_equ`,
-- `erased_node`.

end Tisl.Yield
