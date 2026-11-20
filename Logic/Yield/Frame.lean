/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Policy
public import Logic.Yield.SBisim
public import Logic.CTree.Sim
public import Logic.Interp.Refine

/-!
# Framability through scheduling, projection and translation

Event framability (`Framable`) survives interpretation with framable handler responses, thread
yield/fork erasure, policy scheduling of branch-free framable pools (raw round robin, or any
policy after projecting selections to steps) and event-renaming `translate`
(← `CTree/Interp/Yield/Frame.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction
open ITree (Effect)

/-- Lift an event predicate through a left summand; left events are always admitted. -/
def okE_lift {F E : Effect.{u}} (okE : E.I → Prop) : (F ⊕ₑ E).I → Prop
  | .inl _ => True
  | .inr e => okE e

/-- Source thread signatures nest two event lifts. -/
def okE_thread {F G E : Effect.{u}} (okE : E.I → Prop) : (F ⊕ₑ G ⊕ₑ E).I → Prop :=
  okE_lift (okE_lift okE)

/-- Raw policies preserve left-injected source events and accept every selection. -/
def okE_policy {E : Effect.{0}} (okE : E.I → Prop) : (E ⊕ₑ schedE).I → Prop
  | .inl e => okE e
  | .inr _ => True

section InterpFramable
variable {E F B : Effect.{u}} (h : (e : E.I) → CTree F B (E.O e))

/-- Interpretation preserves finite guarded-step prefixes. -/
theorem guards_to_step_interp {X : Type u} (t : CTree E B X) (ht : guards_to_step t) :
    guards_to_step (interp h t) := by
  induction ht with
  | step t u H => exact .step _ (.guard (interp h u)) (by rw [unfold_interp, H, unfold_step])
  | guard t u H _ ih => exact .guard _ (interp h u) (by rw [unfold_interp, H, unfold_guard]) ih

/-- Framability survives interpretation with framable handler responses. -/
theorem framable_interp {X : Type u} (okE : E.I → Prop) (okF : F.I → Prop)
    (Hh : ∀ e, okE e → Framable okF (h e)) :
    ∀ t : CTree E B X, Framable okE t → Framable okF (interp h t) := fun t ht =>
  coinduction₁ (b := fframable okF) (fun i : {t : CTree E B X // Framable okE t} => interp h i.1)
    (fun R hR IH ⟨t, ht⟩ => by
      have guard_R : ∀ s, Framable okE s → R (.guard (interp h s)) := fun s hs =>
        b_chain hR _ (show framableF okF R (CTree.guard _).unfold by
          rw [unfold_guard]; exact .guard _ (IH ⟨s, hs⟩))
      show framableF okF R (interp h t).unfold
      have Ht := (framable_unfold okE t).1 ht
      cases t with
      | ret x => rw [interp_ret, unfold_pure]; exact .ret x
      | stuck => rw [interp_stuck, unfold_stuck]; exact .stuck
      | step s =>
        rw [unfold_step] at Ht; cases Ht with
        | step _ hs => rw [interp_step, unfold_step]; exact .step _ (guard_R s hs)
      | guard s =>
        rw [unfold_guard] at Ht; cases Ht with
        | guard _ hs => rw [interp_guard, unfold_guard]; exact .guard _ (IH ⟨s, hs⟩)
      | vis e k =>
        rw [unfold_vis] at Ht; cases Ht with
        | vis _ _ he hk =>
          rw [interp_vis]
          exact framable_bind_chain okF (.step hR) (h e) _ (Hh e he) fun x =>
            show framableF okF R (CTree.guard _).unfold by
              rw [unfold_guard]; exact .guard _ (IH ⟨k x, hk x⟩)
      | br c k =>
        rw [unfold_br] at Ht; cases Ht with
        | br _ _ hg hk =>
          rw [interp_br']
          show framableF okF R (CTree.br c fun x => .guard (interp h (k x))).unfold
          rw [unfold_br]
          exact .br c _ (fun y => guards_to_step_guard _ (guards_to_step_interp h _ (hg y)))
            fun y => guard_R _ (hk y))
    ⟨t, ht⟩

end InterpFramable

/-- Erasing thread yield/fork events preserves framability. -/
theorem framable_thread {E B : Effect.{0}} {X : Type} (okE : E.I → Prop)
    (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) (ht : Framable (okE_thread okE) t) :
    Framable okE (interp_thread t) := by
  refine framable_interp handle_yield (okE_lift okE) okE ?_ _
    (framable_interp handle_thread (okE_thread okE) (okE_lift okE) ?_ t ht)
  · rintro (_ | m) he
    · exact fr_ret okE _
    · exact fr_vis okE m pure he fun x => fr_ret okE x
  · rintro (y | _ | m) he
    · show Framable _ (CTree.vis _ _); exact fr_vis _ _ _ trivial fun x => fr_ret _ x
    · exact fr_ret _ _
    · show Framable _ (CTree.vis _ _); exact fr_vis _ _ _ he fun x => fr_ret _ x

section PoolFramable
variable {E B : Effect.{0}} (okE : E.I → Prop)

/-- Every thread in the pool is framable. -/
def pool_framable {n : Nat} (v : Pool E B n) : Prop :=
  ∀ i : Fin n, Framable (okE_thread okE) v[i]

/-- Replacing a slot with a framable thread preserves pool framability. -/
theorem pool_framable_replace {n} (v : Pool E B n) (i : Fin n) (t : Thread E B)
    (hv : pool_framable okE v) (ht : Framable (okE_thread okE) t) :
    pool_framable okE (v.set i t) :=
  vector_replace_pointwise (fun a _ : Thread E B => Framable (okE_thread okE) a) v v i t t
    (fun j _ => hv j) ht

/-- Removing a slot preserves pool framability. -/
theorem pool_framable_remove {n} (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (hv : pool_framable okE v) : pool_framable okE (v.eraseIdx i) :=
  vector_remove_pointwise (fun a _ : Thread E B => Framable (okE_thread okE) a) v v i
    (fun j _ => hv j)

/-- Prepending a framable thread preserves pool framability. -/
theorem pool_framable_cons {n} (t : Thread E B) (v : Pool E B n)
    (ht : Framable (okE_thread okE) t) (hv : pool_framable okE v) :
    pool_framable okE (Vector.cons t v) :=
  vector_cons_pointwise (fun a _ : Thread E B => Framable (okE_thread okE) a) t t v v ht hv

/-- Every policy preserves framability after projecting selections to steps. -/
theorem framable_schedule [Bn -< B] (sch : Scheduler) (n : Nat) (ts : Pool E B n)
    (focus : Option (Fin n)) (st : sch.sched_state) (hbf : pool_branchfree ts)
    (hfr : pool_framable okE ts) :
    Framable okE (project_scheduled (schedule_policy sch n ts focus st)) := by
  let P : CTree E B PUnit → Prop := fun x => ∃ (n : Nat) (ts : Pool E B n) (focus : Option (Fin n))
    (st : sch.sched_state), pool_branchfree ts ∧ pool_framable okE ts ∧
      x = project_scheduled (schedule_policy sch n ts focus st)
  refine coinduction₁ (b := fframable okE) (fun i : {x // P x} => i.1) ?_
    ⟨_, n, ts, focus, st, hbf, hfr, rfl⟩
  rintro R hR IH ⟨_, n, ts, focus, st, hbf, hfr, rfl⟩
  have ih : ∀ n (ts : Pool E B n) focus st, pool_branchfree ts → pool_framable okE ts →
      R (project_scheduled (schedule_policy sch n ts focus st)) :=
    fun n ts focus st hb hf => IH ⟨_, n, ts, focus, st, hb, hf, rfl⟩
  have guard_R : ∀ x, R x → R (.guard x) := fun x hx => b_chain hR _
    (show framableF okE R (CTree.guard _).unfold by rw [unfold_guard]; exact .guard _ hx)
  have sched_R : ∀ j (k : PUnit → CTree (E ⊕ₑ schedE) B PUnit), R (project_scheduled (k ⟨⟩)) →
      R (project_scheduled (.vis (.inr j) k)) := fun j k hk => by
    rw [project_scheduled_scheduled]
    exact b_chain hR _ (show framableF okE R (CTree.step _).unfold by
      rw [unfold_step]; exact .step _ (guard_R _ hk))
  have sched_gts : ∀ j (k : PUnit → CTree (E ⊕ₑ schedE) B PUnit),
      guards_to_step (project_scheduled (.vis (.inr j) k)) := fun j k =>
    .step _ _ (by rw [project_scheduled_scheduled, unfold_step])
  show framableF okE R (project_scheduled (schedule_policy sch n ts focus st)).unfold
  rcases focus with _ | i
  · cases n with
    | zero =>
      rw [schedule_policy_empty_equ]
      exact (show framableF okE R (project_scheduled (pure ⟨⟩ : CTree _ B PUnit)).unfold by
        rw [project_scheduled_ret, unfold_pure]; exact .ret _)
    | succ n =>
      rw [schedule_policy_no_focus_equ]
      generalize sch.sched_pick n st = pick
      generalize sch.sched_arity n st = a at pick
      cases a with
      | zero =>
        show framableF okE R (project_scheduled (.vis (.inr _) fun _ => _)).unfold
        rw [project_scheduled_scheduled, unfold_step]
        exact .step _ (guard_R _ (ih _ _ _ _ hbf hfr))
      | succ a =>
        show framableF okE R (project_scheduled (CTree.br _ fun x => _)).unfold
        rw [project_scheduled_br, unfold_br]
        exact .br _ _ (fun y => guards_to_step_guard _ (sched_gts _ _))
          fun y => guard_R _ (sched_R _ _ (ih _ _ _ _ hbf hfr))
  · cases n with
    | zero => exact i.elim0
    | succ n =>
      have Hi := (branchfree_unfold _).1 (hbf i)
      have Hfi := (framable_unfold _ _).1 (hfr i)
      generalize hobs : ts[i].unfold = ot at Hi Hfi
      cases Hi with
      | ret x =>
        rw [schedule_policy_focused_ret_equ sch n ts i st hobs, project_scheduled_guard,
          unfold_guard]
        exact .guard _ (ih _ _ _ _ (pool_branchfree_remove _ i hbf)
          (pool_framable_remove okE _ i hfr))
      | stuck =>
        rw [schedule_policy_focused_stuck_equ sch n ts i st hobs, project_scheduled_stuck,
          unfold_stuck]
        exact .stuck
      | step t ht =>
        cases Hfi with
        | step _ hft =>
          rw [schedule_policy_focused_step_equ sch n ts i t st hobs, project_scheduled_step,
            unfold_step]
          exact .step _ (guard_R _ (ih _ _ _ _ (pool_branchfree_replace _ i t hbf ht)
            (pool_framable_replace okE _ i t hfr hft)))
      | guard t ht =>
        cases Hfi with
        | guard _ hft =>
          rw [schedule_policy_focused_guard_equ sch n ts i t st hobs, project_scheduled_guard,
            unfold_guard]
          exact .guard _ (ih _ _ _ _ (pool_branchfree_replace _ i t hbf ht)
            (pool_framable_replace okE _ i t hfr hft))
      | vis e k hk =>
        cases Hfi with
        | vis _ _ he hfk =>
          rcases e with ⟨⟩ | ⟨⟩ | e
          · rw [schedule_policy_focused_yield_equ sch n ts i k st hobs, project_scheduled_guard,
              unfold_guard]
            exact .guard _ (ih _ _ _ _ (pool_branchfree_replace _ i _ hbf (hk _))
              (pool_framable_replace okE _ i _ hfr (hfk _)))
          · rw [schedule_policy_focused_fork_equ sch n ts i k st hobs, project_scheduled_guard,
              unfold_guard]
            exact .guard _ (ih _ _ _ _
              (pool_branchfree_cons _ _ (hk true) (pool_branchfree_replace _ i _ hbf (hk false)))
              (pool_framable_cons okE _ _ (hfk true)
                (pool_framable_replace okE _ i _ hfr (hfk false))))
          · rw [schedule_policy_focused_user_event_equ sch n ts i e k st hobs,
              project_scheduled_user, unfold_vis]
            exact .vis e _ he fun x => guard_R _ (ih _ _ _ _
              (pool_branchfree_replace _ i _ hbf (hk x))
              (pool_framable_replace okE _ i _ hfr (hfk x)))

end PoolFramable

/-- Deterministic round robin adds admissible selections and preserves source nodes. -/
theorem framable_schedule_rr {E : Effect.{0}} (okE : E.I → Prop) (n : Nat) (ts : Pool E Bn n)
    (focus : Option (Fin n)) (cursor : Nat) (hbf : pool_branchfree ts)
    (hfr : pool_framable okE ts) :
    Framable (okE_policy okE) (schedule_policy rr_scheduler n ts focus cursor) := by
  -- `schedule_rr` keeps the cursor at type `Nat` (`rr_scheduler.sched_state` does not reduce
  -- under `rw`).
  show Framable _ (schedule_rr n ts focus cursor)
  let P : Completed E Bn → Prop := fun x => ∃ (n : Nat) (ts : Pool E Bn n)
    (focus : Option (Fin n)) (cursor : Nat), pool_branchfree ts ∧ pool_framable okE ts ∧
      x = schedule_rr n ts focus cursor
  refine coinduction₁ (b := fframable (okE_policy okE)) (fun i : {x // P x} => i.1) ?_
    ⟨_, n, ts, focus, cursor, hbf, hfr, rfl⟩
  rintro R hR IH ⟨_, n, ts, focus, cursor, hbf, hfr, rfl⟩
  have ih : ∀ n (ts : Pool E Bn n) focus cursor, pool_branchfree ts → pool_framable okE ts →
      R (schedule_rr n ts focus cursor) :=
    fun n ts focus cursor hb hf => IH ⟨_, n, ts, focus, cursor, hb, hf, rfl⟩
  show framableF (okE_policy okE) R (schedule_rr n ts focus cursor).unfold
  rcases focus with _ | i
  · cases n with
    | zero => rw [schedule_rr_empty_none]; exact .ret _
    | succ n =>
      rw [schedule_rr_no_focus_nonempty]
      exact .vis _ _ trivial fun _ => ih _ _ _ _ hbf hfr
  · cases n with
    | zero => exact i.elim0
    | succ n =>
      have Hi := (branchfree_unfold _).1 (hbf i)
      have Hfi := (framable_unfold _ _).1 (hfr i)
      generalize hobs : ts[i].unfold = ot at Hi Hfi
      cases Hi with
      | ret x =>
        rw [schedule_rr_focused_ret n ts i cursor hobs]
        exact .guard _ (ih _ _ _ _ (pool_branchfree_remove _ i hbf)
          (pool_framable_remove okE _ i hfr))
      | stuck =>
        rw [schedule_rr_focused_stuck n ts i cursor hobs]; exact .stuck
      | step t ht =>
        cases Hfi with
        | step _ hft =>
          rw [schedule_rr_focused_step n ts i t cursor hobs]
          exact .step _ (ih _ _ _ _ (pool_branchfree_replace _ i t hbf ht)
            (pool_framable_replace okE _ i t hfr hft))
      | guard t ht =>
        cases Hfi with
        | guard _ hft =>
          rw [schedule_rr_focused_guard n ts i t cursor hobs]
          exact .guard _ (ih _ _ _ _ (pool_branchfree_replace _ i t hbf ht)
            (pool_framable_replace okE _ i t hfr hft))
      | vis e k hk =>
        cases Hfi with
        | vis _ _ he hfk =>
          rcases e with ⟨⟩ | ⟨⟩ | e
          · rw [schedule_rr_focused_yield n ts i k cursor hobs]
            exact .guard _ (ih _ _ _ _ (pool_branchfree_replace _ i _ hbf (hk _))
              (pool_framable_replace okE _ i _ hfr (hfk _)))
          · rw [schedule_rr_focused_fork n ts i k cursor hobs]
            exact .guard _ (ih _ _ _ _
              (pool_branchfree_cons _ _ (hk true) (pool_branchfree_replace _ i _ hbf (hk false)))
              (pool_framable_cons okE _ _ (hfk true)
                (pool_framable_replace okE _ i _ hfr (hfk false))))
          · rw [schedule_rr_focused_user_event n ts i e k cursor hobs]
            exact .vis _ _ he fun x => ih _ _ _ _ (pool_branchfree_replace _ i _ hbf (hk x))
              (pool_framable_replace okE _ i _ hfr (hfk x))

section TranslateFramable
variable {E F B : Effect.{u}} {X : Type u}

/-- Translation preserves finite guarded-step prefixes. -/
theorem guards_to_step_translate (f : (e : E.I) → (f : F.I) × (F.O f → E.O e)) (t : CTree E B X)
    (ht : guards_to_step t) : guards_to_step (translate f t) := by
  induction ht with
  | step t u H => exact .step _ (translate f u) (by rw [unfold_translate, H, unfold_step])
  | guard t u H _ ih =>
    exact .guard _ (translate f u) (by rw [unfold_translate, H, unfold_guard]) ih

/-- One framable node of `translate f t` from one of `t`, if `f` maps admissible events to
admissible events (shared body of the two `framable_translate_*` theorems). -/
private theorem framable_translate (f : (e : E.I) → (f : F.I) × (F.O f → E.O e))
    (okE : E.I → Prop) (okF : F.I → Prop) (hf : ∀ e, okE e → okF (f e).1) :
    ∀ t : CTree E B X, Framable okE t → Framable okF (translate f t) := fun t ht =>
  coinduction₁ (b := fframable okF) (fun i : {t : CTree E B X // Framable okE t} => translate f i.1)
    (fun R _ IH ⟨t, ht⟩ => by
      show framableF okF R (translate f t).unfold
      have Ht := (framable_unfold okE t).1 ht
      cases t with
      | ret x => rw [translate_ret, unfold_pure]; exact .ret x
      | stuck => rw [translate_stuck, unfold_stuck]; exact .stuck
      | step s =>
        rw [unfold_step] at Ht; cases Ht with
        | step _ hs => rw [translate_step, unfold_step]; exact .step _ (IH ⟨s, hs⟩)
      | guard s =>
        rw [unfold_guard] at Ht; cases Ht with
        | guard _ hs => rw [translate_guard, unfold_guard]; exact .guard _ (IH ⟨s, hs⟩)
      | vis e k =>
        rw [unfold_vis] at Ht; cases Ht with
        | vis _ _ he hk =>
          rw [translate_vis, unfold_vis]; exact .vis _ _ (hf e he) fun x => IH ⟨_, hk _⟩
      | br c k =>
        rw [unfold_br] at Ht; cases Ht with
        | br _ _ hg hk =>
          rw [translate_br, unfold_br]
          exact .br c _ (fun y => guards_to_step_translate f _ (hg y)) fun y => IH ⟨_, hk y⟩)
    ⟨t, ht⟩

/-- Embedding a tree's events under a right summand preserves framability. -/
theorem framable_translate_inr1 (okE : E.I → Prop) (t : CTree E B X) (ht : Framable okE t) :
    Framable (okE_lift (F := F) okE)
      (translate (fun e => (⟨.inr e, id⟩ : (f : (F ⊕ₑ E).I) × ((F ⊕ₑ E).O f → E.O e))) t) :=
  framable_translate _ okE _ (fun _ he => he) t ht

end TranslateFramable

/-- Embedding source events under the policy's left summand frames. -/
theorem framable_translate_inl1 {E B : Effect.{0}} {X : Type} (okE : E.I → Prop)
    (t : CTree E B X) (ht : Framable okE t) :
    Framable (okE_policy okE)
      (translate (fun e => (⟨.inl e, id⟩ : (f : (E ⊕ₑ schedE).I) × ((E ⊕ₑ schedE).O f → E.O e)))
        t) :=
  framable_translate _ okE _ (fun _ he => he) t ht

/-- Nondeterministic scheduler erasure preserves framability. -/
theorem framable_erased_nd {E B : Effect.{0}} [Bn -< B] (okE : E.I → Prop) (n : Nat)
    (ts : Pool E B n) (focus : Option (Fin n)) (hbf : pool_branchfree ts)
    (hfr : pool_framable okE ts) : Framable okE (project_scheduled (schedule n ts focus)) :=
  framable_schedule okE nd_scheduler n ts focus ⟨⟩ hbf hfr

/-- Round-robin scheduler erasure preserves framability. -/
theorem framable_erased_rr {E : Effect.{0}} (okE : E.I → Prop) (n : Nat) (ts : Pool E Bn n)
    (focus : Option (Fin n)) (cursor : Nat) (hbf : pool_branchfree ts)
    (hfr : pool_framable okE ts) :
    Framable okE (project_scheduled (schedule_rr n ts focus cursor)) :=
  framable_schedule okE rr_scheduler n ts focus cursor hbf hfr

-- Not ported: `framable_handler` (Ltac; the handler obligations of `framable_thread` are proved
-- inline). `framable_translate` is a private shared body of `framable_translate_inr1/inl1`.

end Tisl.Yield
