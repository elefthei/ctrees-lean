/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.RoundRobin
public import Logic.Yield.Nondeterministic
public import Logic.CTree.Sim

/-!
# Sequential thread segments and the cooperative prefix equation

A `Sequential` raw thread has no yield, fork or hidden branch anywhere: only returns, `stuck`,
guards, visible steps and user events. A focused pool slot whose head segment is sequential runs
in the scheduled pool exactly as its standalone erased run (`interp_thread`), then rejoins the
pool with the residual continuation, for every scheduler (← `CTree/Interp/Yield/Sequential.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction
open ITree (Effect)

/-! ## Sequential threads -/

section SequentialThreads
variable {E B : Effect.{0}} {X : Type}

/-- Only user events: yields and forks are rejected. -/
def user_only : (yieldE ⊕ₑ forkE ⊕ₑ E).I → Prop
  | .inr (.inr _) => True
  | _ => False

/-- A sequential raw thread is branch-free and has no yield/fork events; reuses the existing
coinductive predicates instead of a third tower. -/
def Sequential (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) : Prop :=
  BranchFree t ∧ Framable user_only t

/-- Node shapes of a sequential thread, for inversion only (Rocq `sequentialF`). -/
inductive SequentialF (R : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X → Prop) :
    CTreeF (yieldE ⊕ₑ forkE ⊕ₑ E) B X (CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) → Prop
  | ret (x : X) : SequentialF R (.ret x)
  | stuck : SequentialF R .stuck
  | guard (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) : R t → SequentialF R (.guard t)
  | step (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) : R t → SequentialF R (.step t)
  | vis (e : E.I) (k : E.O e → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) :
      (∀ y, R (k y)) → SequentialF R (.vis (.inr (.inr e)) k)

/-- Expose the node of a branch-free, user-only thread. -/
theorem sequential_inv (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) (h : Sequential t) :
    SequentialF Sequential t.unfold := by
  obtain ⟨hb, hf⟩ := h
  rw [branchfree_unfold] at hb
  rw [framable_unfold] at hf
  generalize t.unfold = ot at hb hf
  cases hb with
  | ret x => exact .ret x
  | stuck => exact .stuck
  | step t hb => cases hf with | step _ hf => exact .step t ⟨hb, hf⟩
  | guard t hb => cases hf with | guard _ hf => exact .guard t ⟨hb, hf⟩
  | vis e k hb =>
    cases hf with
    | vis _ _ hok hf =>
      rcases e with _ | _ | e
      · exact (hok : False).elim
      · exact (hok : False).elim
      · exact .vis e k fun y => ⟨hb y, hf y⟩

end SequentialThreads

/-! ## Erasure of a standalone thread, node by node (`interp_thread`) -/

section ThreadNodes
variable {E B : Effect.{0}} {X : Type}

/-- Standalone erasure of a stuck thread is stuck. -/
theorem interp_thread_stuck_node :
    interp_thread (.stuck : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) = .stuck := by
  simp [interp_thread, interp_yield]

/-- Standalone erasure commutes with a leading guard. -/
theorem interp_thread_guard_node (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) :
    interp_thread (.guard t) = .guard (interp_thread t) := by
  simp [interp_thread, interp_yield]

/-- Standalone erasure turns a visible step into a step followed by two guards. -/
theorem interp_thread_step_node (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) :
    interp_thread (.step t) = .step (.guard (.guard (interp_thread t))) := by
  simp [interp_thread, interp_yield]

end ThreadNodes

/-! ## Guard alignment closed under a shared bind prefix

`AlignRel Base` relates `Base` pairs under any number of leading guards, identical trees, and any
pair with the same prefix `h` whose continuations are themselves related. It is a `galigned`
post-fixpoint whenever every `Base` pair aligns, hence is contained in `~`. -/

section AlignBind
variable {F B : Effect.{u}} {X : Type u} (Base : CTree F B X → CTree F B X → Prop)

/-- Close a base relation under leading guards, equality, and shared bind prefixes with related
continuations: exactly one scheduler turn (Rocq `align_rel`). -/
inductive AlignRel : CTree F B X → CTree F B X → Prop
  | at (a b : Nat) (t u T U : CTree F B X) :
      Base t u → T = guards a t → U = guards b u → AlignRel T U
  | equ (T U : CTree F B X) : T = U → AlignRel T U
  | bind (a b : Nat) {Z : Type u} (h : CTree F B Z) (f g : Z → CTree F B X) (T U : CTree F B X) :
      (∀ z, AlignRel (f z) (g z)) →
      T = guards a (h >>= fun z => .guard (f z)) →
      U = guards b (h >>= fun z => .guard (g z)) →
      AlignRel T U

/-- Equal trees have aligned nodes. -/
theorem align_equ_step (T U : CTree F B X) (H : T = U) : GalignF (AlignRel Base) T U := by
  subst H
  cases T with
  | ret r => exact .ret 0 0 r rfl rfl
  | stuck => exact .stuck 0 0 rfl rfl
  | step s => exact .step 0 0 s s rfl rfl (.equ s s rfl)
  | guard g => exact .guard 0 0 g g rfl rfl (.equ g g rfl)
  | vis e k => exact .vis 0 0 e k k rfl rfl fun x => .equ _ _ rfl
  | br c k => exact .br 0 0 c k k rfl rfl fun x => .equ _ _ rfl

/-- A common bind prefix with related continuations has aligned nodes. -/
theorem align_bind_step (a b : Nat) {Z : Type u} (h : CTree F B Z) (f g : Z → CTree F B X)
    (T U : CTree F B X) (Hfg : ∀ z, AlignRel Base (f z) (g z))
    (ET : T = guards a (h >>= fun z => .guard (f z)))
    (EU : U = guards b (h >>= fun z => .guard (g z))) : GalignF (AlignRel Base) T U := by
  subst ET EU
  cases h with
  | ret z =>
    refine .guard a b (f z) (g z) ?_ ?_ (Hfg z) <;>
      simp only [pure_bind', guards_guard]
  | stuck => exact .stuck a b (by rw [stuck_bind]) (by rw [stuck_bind])
  | step s =>
    exact .step a b _ _ (by rw [step_bind]; rfl) (by rw [step_bind]; rfl)
      (.bind 0 0 s f g _ _ Hfg rfl rfl)
  | guard g' =>
    exact .guard a b _ _ (by rw [guard_bind, guards_guard]; rfl)
      (by rw [guard_bind, guards_guard]; rfl) (.bind 0 0 g' f g _ _ Hfg rfl rfl)
  | vis e kk =>
    exact .vis a b e _ _ (by rw [vis_bind]; rfl) (by rw [vis_bind]; rfl)
      fun w => .bind 0 0 (kk w) f g _ _ Hfg rfl rfl
  | br c kk =>
    exact .br a b c _ _ (by rw [br_bind]; rfl) (by rw [br_bind]; rfl)
      fun w => .bind 0 0 (kk w) f g _ _ Hfg rfl rfl

/-- Leading finite guard prefixes preserve node alignment. -/
theorem galignF_guards (a b : Nat) (t u T U : CTree F B X) (H : GalignF (AlignRel Base) t u)
    (ET : T = guards a t) (EU : U = guards b u) : GalignF (AlignRel Base) T U := by
  subst ET EU
  cases H with
  | guard n m t' u' El Er H =>
    subst El Er; exact .guard (a + n) (b + m) t' u' (guards_shift a n t') (guards_shift b m u') H
  | ret n m r El Er =>
    subst El Er; exact .ret (a + n) (b + m) r (guards_add ..).symm (guards_add ..).symm
  | br n m c k k' El Er H =>
    subst El Er; exact .br (a + n) (b + m) c k k' (guards_add ..).symm (guards_add ..).symm H
  | vis n m e k k' El Er H =>
    subst El Er; exact .vis (a + n) (b + m) e k k' (guards_add ..).symm (guards_add ..).symm H
  | stuck n m El Er =>
    subst El Er; exact .stuck (a + n) (b + m) (guards_add ..).symm (guards_add ..).symm
  | step n m t' u' El Er H =>
    subst El Er; exact .step (a + n) (b + m) t' u' (guards_add ..).symm (guards_add ..).symm H

/-- The alignment closure is a post-fixpoint when every base pair aligns. -/
theorem align_rel_step (Hbase : ∀ t u, Base t u → GalignF (AlignRel Base) t u) (T U : CTree F B X)
    (H : AlignRel Base T U) : GalignF (AlignRel Base) T U := by
  cases H with
  | «at» a b t u T U Hb ET EU => exact galignF_guards Base a b t u T U (Hbase t u Hb) ET EU
  | equ T U H => exact align_equ_step Base T U H
  | bind a b h f g T U Hfg ET EU => exact align_bind_step Base a b h f g T U Hfg ET EU

end AlignBind

/-! ## The cooperative prefix equation, generically over the scheduling policy

A focused sequential segment preserves the policy state until it rejoins the pool; the scheduled
observations are projected to silent steps. -/

section Prefix
variable {E F B : Effect.{0}} [Bn -< B] {Sg : Type}
  (handler : (e : E.I) → StateT Sg (CTree F B) (E.O e))
  (sch : Scheduler) (st : sch.sched_state) (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1))
  {Y : Type} (K : Y → Thread E B)

-- Run the focused pool under the direct scheduling policy (Rocq section-local `run`).
set_option hygiene false in
local notation:max "run " us:max σ:max =>
  interp_state handler (project_scheduled (schedule_policy sch (n + 1) us (some i) st)) σ

/-- Exact congruence for one focused node. -/
theorem run_slot_equ (t t' : Thread E B) (σ : Sg) (H : t = t') :
    run (ts.set i t) σ = run (ts.set i t') σ := by
  rw [H]

/-- Exact equation for a focused stuck node. -/
theorem run_slot_stuck (t : Thread E B) (σ : Sg) (H : t = .stuck) :
    run (ts.set i t) σ = .stuck := by
  subst H
  rw [schedule_policy_focused_stuck_equ sch n _ i st (by simp)]
  simp

/-- Exact equation for a focused guard. -/
theorem run_slot_guard (t : Thread E B) (σ : Sg) :
    run (ts.set i (.guard t)) σ = .guard (run (ts.set i t) σ) := by
  rw [schedule_policy_focused_guard_equ sch n _ i t st (by simp)]
  simp [Vector.set_set]

/-- Exact equation for a focused step. -/
theorem run_slot_step (t : Thread E B) (σ : Sg) :
    run (ts.set i (.step t)) σ = .step (.guard (.guard (run (ts.set i t) σ))) := by
  rw [schedule_policy_focused_step_equ sch n _ i t st (by simp)]
  simp [Vector.set_set]

/-- Exact equation for a focused user event. -/
theorem run_slot_user (e : E.I) (k : E.O e → Thread E B) (σ : Sg) :
    run (ts.set i (.vis (.inr (.inr e)) k)) σ =
      (handler e σ >>= fun p => .guard (.guard (run (ts.set i (k p.1)) p.2))) := by
  rw [schedule_policy_focused_user_event_equ sch n _ i e k st (by simp)]
  simp [Vector.set_set]

/-- Scheduled sequential segment versus its standalone erased run followed by rejoin
(Rocq `prefix_base`). -/
inductive PrefixBase : CTree F B (PUnit × Sg) → CTree F B (PUnit × Sg) → Prop
  | at (w : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B Y) (σ : Sg) :
      Sequential w →
      PrefixBase (run (ts.set i (w >>= K)) σ)
        (interp_state handler (interp_thread w) σ >>= fun p => run (ts.set i (K p.1)) p.2)

/-- One node of a sequential segment aligns the scheduled and standalone runs. -/
theorem prefix_base_step (t u : CTree F B (PUnit × Sg))
    (H : PrefixBase handler sch st n ts i K t u) :
    GalignF (AlignRel (PrefixBase handler sch st n ts i K)) t u := by
  obtain ⟨w, σ, hw⟩ := H
  have hs := sequential_inv w hw
  cases w with
  | ret y =>
    refine align_equ_step _ _ _ ?_
    simp [interp_state_thread_ret]
  | stuck =>
    exact .stuck 0 0 (run_slot_stuck handler sch st n ts i _ σ (by simp))
      (by simp [interp_thread_stuck_node])
  | guard w' =>
    rw [unfold_guard] at hs
    cases hs with
    | guard _ hw' =>
      refine .guard 0 0 _ _ ?_ ?_ (.at 0 0 _ _ _ _ (.at w' σ hw') rfl rfl)
      · rw [guard_bind, run_slot_guard]; rfl
      · rw [interp_thread_guard_node, interp_state_guard, guard_bind]; rfl
  | step w' =>
    rw [unfold_step] at hs
    cases hs with
    | step _ hw' =>
      refine .step 0 0 _ _ ?_ ?_ (.at 2 3 _ _ _ _ (.at w' σ hw') rfl rfl)
      · rw [step_bind, run_slot_step]; rfl
      · simp only [interp_thread_step_node, interp_state_step, interp_state_guard, step_bind,
          guard_bind]
        rfl
  | vis e k =>
    rw [unfold_vis] at hs
    cases hs with
    | vis e k hk =>
      refine align_bind_step _ 0 0 (handler e σ)
        (fun p => .guard (run (ts.set i (k p.1 >>= K)) p.2))
        (fun p => .guard (.guard (interp_state handler (interp_thread (k p.1)) p.2 >>=
          fun q => run (ts.set i (K q.1)) q.2))) _ _
        (fun p => .at 1 2 _ _ _ _ (.at (k p.1) p.2 (hk _)) rfl rfl) ?_ ?_
      · rw [vis_bind, run_slot_user]; rfl
      · simp only [interp_thread_user_node, interp_state_vis, bind_assoc, guard_bind,
          interp_state_guard]
        rfl
  | br c k => rw [unfold_br] at hs; cases hs

/-- A focused sequential segment runs standalone and then rejoins its pool. -/
theorem run_prefix_bind (w : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B Y) (σ : Sg) (hw : Sequential w) :
    run (ts.set i (w >>= K)) σ ~
      (interp_state handler (interp_thread w) σ >>= fun p => run (ts.set i (K p.1)) p.2) :=
  galigned_sbisim _ _ <| galigned_coind (AlignRel (PrefixBase handler sch st n ts i K))
    (align_rel_step _ (prefix_base_step handler sch st n ts i K)) _ _
    (.at 0 0 _ _ _ _ (.at w σ hw) rfl rfl)

end Prefix

/-! ## The prefix equation for the instrumented policy runner

A focused sequential interval never invokes the policy. Its observations are only relabelled user
logs, with the same actual pool continuation. -/

section FairPrefix
variable {E : Effect.{0}} {W Sg X : Type} (sch : Scheduler)
  (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))
  (st : sch.sched_state) (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
  (K : X → Thread E Bn)

set_option hygiene false in
local notation:max "run " us:max σ:max => interp_schedule_fair sch handler (n + 1) us (some i) st σ

theorem fair_prefix_slot_equ (t u : Thread E Bn) (σ : Sg) (H : t = u) :
    run (ts.set i t) σ = run (ts.set i u) σ := by
  rw [H]

theorem fair_prefix_slot_guard (t : Thread E Bn) (σ : Sg) :
    run (ts.set i (.guard t)) σ = .guard (run (ts.set i t) σ) := by
  rw [interp_schedule_fair_guard_exact sch handler n _ i t st σ (by simp), Vector.set_set]

theorem fair_prefix_slot_step (t : Thread E Bn) (σ : Sg) :
    run (ts.set i (.step t)) σ = .step (.guard (run (ts.set i t) σ)) := by
  rw [interp_schedule_fair_step_exact sch handler n _ i t st σ (by simp), Vector.set_set]

theorem fair_prefix_slot_user (e : E.I) (k : E.O e → Thread E Bn) (σ : Sg) :
    run (ts.set i (.vis (.inr (.inr e)) k)) σ =
      (translate relabel_log (handler e σ) >>= fun p => .guard (run (ts.set i (k p.1)) p.2)) := by
  rw [interp_schedule_fair_user_exact sch handler n _ i e k st σ (by simp)]
  simp only [Vector.set_set]

/-- Scheduled sequential segment versus its relabelled standalone run followed by rejoin
(Rocq `fair_prefix_base`). -/
inductive FairPrefixBase : ctreeW (W ⊕ Nat) Bn (PUnit × Sg) → ctreeW (W ⊕ Nat) Bn (PUnit × Sg) →
    Prop
  | at (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) Bn X) (σ : Sg) :
      Sequential t →
      FairPrefixBase (run (ts.set i (t >>= K)) σ)
        (translate relabel_log (interp_state handler (interp_thread t) σ) >>= fun p =>
          run (ts.set i (K p.1)) p.2)

theorem fair_prefix_base_step (T U : ctreeW (W ⊕ Nat) Bn (PUnit × Sg))
    (H : FairPrefixBase sch handler st n ts i K T U) :
    GalignF (AlignRel (FairPrefixBase sch handler st n ts i K)) T U := by
  obtain ⟨t, σ, ht⟩ := H
  have hs := sequential_inv t ht
  cases t with
  | ret x =>
    refine align_equ_step _ _ _ ?_
    simp [interp_state_thread_ret]
  | stuck =>
    exact .stuck 0 0 (interp_schedule_fair_stuck sch handler n _ i st σ (by simp))
      (by simp [interp_thread_stuck_node])
  | guard t' =>
    rw [unfold_guard] at hs
    cases hs with
    | guard _ ht' =>
      refine .guard 0 0 _ _ ?_ ?_ (.at 0 0 _ _ _ _ (.at t' σ ht') rfl rfl)
      · rw [guard_bind, fair_prefix_slot_guard]; rfl
      · rw [interp_thread_guard_node, interp_state_guard, translate_guard, guard_bind]; rfl
  | step t' =>
    rw [unfold_step] at hs
    cases hs with
    | step _ ht' =>
      refine .step 0 0 _ _ ?_ ?_ (.at 1 3 _ _ _ _ (.at t' σ ht') rfl rfl)
      · rw [step_bind, fair_prefix_slot_step]; rfl
      · simp only [interp_thread_step_node, interp_state_step, interp_state_guard, translate_step,
          translate_guard, step_bind, guard_bind]
        rfl
  | vis e k =>
    rw [unfold_vis] at hs
    cases hs with
    | vis e k hk =>
      refine align_bind_step _ 0 0 (translate relabel_log (handler e σ))
        (fun p => run (ts.set i (k p.1 >>= K)) p.2)
        (fun p => guards 2 (translate relabel_log
          (interp_state handler (interp_thread (k p.1)) p.2) >>= fun q =>
            run (ts.set i (K q.1)) q.2))
        _ _ (fun p => .at 0 2 _ _ _ _ (.at (k p.1) p.2 (hk _)) rfl rfl) ?_ ?_
      · rw [vis_bind, fair_prefix_slot_user]; rfl
      · simp only [interp_thread_user_node, interp_state_vis, translate_bind, bind_assoc,
          translate_guard, guard_bind, interp_state_guard]
        rfl
  | br c k => rw [unfold_br] at hs; cases hs

theorem fair_prefix_bind (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) Bn X) (σ : Sg) (ht : Sequential t) :
    run (ts.set i (t >>= K)) σ ~
      (translate relabel_log (interp_state handler (interp_thread t) σ) >>= fun p =>
        run (ts.set i (K p.1)) p.2) :=
  galigned_sbisim _ _ <| galigned_coind (AlignRel (FairPrefixBase sch handler st n ts i K))
    (align_rel_step _ (fair_prefix_base_step sch handler st n ts i K)) _ _
    (.at 0 0 _ _ _ _ (.at t σ ht) rfl rfl)

end FairPrefix

/-- Policy-generic join principle for a focused sequential segment. -/
theorem interp_schedule_fair_prefix_bind {E : Effect.{0}} {W Sg X : Type} (sch : Scheduler)
    (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) (n : Nat) (ts : Pool E Bn (n + 1))
    (i : Fin (n + 1)) (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) Bn X) (K : X → Thread E Bn)
    (st : sch.sched_state) (σ : Sg) (ht : Sequential t) :
    interp_schedule_fair sch handler (n + 1) (ts.set i (t >>= K)) (some i) st σ ~
      (translate relabel_log (interp_state handler (interp_thread t) σ) >>= fun p =>
        interp_schedule_fair sch handler (n + 1) (ts.set i (K p.1)) (some i) st p.2) :=
  fair_prefix_bind sch handler st n ts i K t σ ht

/-- Round-robin join principle for a focused sequential segment. -/
theorem interp_schedule_rr_prefix_bind {E : Effect.{0}} {W Sg : Type}
    (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) (n : Nat) (ts : Pool E Bn (n + 1))
    (i : Fin (n + 1)) {Y : Type} (w : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) Bn Y) (K : Y → Thread E Bn)
    (m : Nat) (σ : Sg) (hw : Sequential w) :
    interp_schedule_rr handler (n + 1) (ts.set i (w >>= K)) (some i) m σ ~
      (translate relabel_log (interp_state handler (interp_thread w) σ) >>= fun p =>
        interp_schedule_rr handler (n + 1) (ts.set i (K p.1)) (some i) m p.2) :=
  interp_schedule_fair_prefix_bind rr_scheduler handler n ts i w K m σ hw

/-- Nondeterministic join principle for a focused sequential segment. -/
theorem interp_schedule_nd_prefix_bind {E F B : Effect.{0}} [Bn -< B] {Sg : Type}
    (handler : (e : E.I) → StateT Sg (CTree F B) (E.O e)) (n : Nat) (ts : Pool E B (n + 1))
    (i : Fin (n + 1)) {Y : Type} (w : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B Y) (K : Y → Thread E B)
    (σ : Sg) (hw : Sequential w) :
    interp_schedule_nd handler (n + 1) (ts.set i (w >>= K)) (some i) σ ~
      (interp_state handler (interp_thread w) σ >>= fun p =>
        interp_schedule_nd handler (n + 1) (ts.set i (K p.1)) (some i) p.2) :=
  run_prefix_bind handler nd_scheduler ⟨⟩ n ts i K w σ hw

end Tisl.Yield

-- Not ported as declarations: the section-local `Let run` (Prefix) and `Local Notation run`
-- (FairPrefix) are `local notation`s; `Let rhs_k` is inlined as
-- `fun p => run (ts.set i (K p.1)) p.2`.
