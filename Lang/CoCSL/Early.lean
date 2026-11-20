/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.RunnersFair
public import Logic.CTree.Bind

/-!
# CoCSL early temporal rules and expression equations

Observable emission and cooperative selection rules (`an/au/ag_csl_{nd,rr}_{emit,yield}`), the
first-fit allocation rules of finite heaps, the arithmetic/eval/if/alloc/guard focused equations
of the ND runner and of the policy kernel (with their round-robin instances) and the one-unroll
`while` equations (← `Lang/CoCSL/Mod.v`, lines 1684-2204).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx Tisl.Notation
open ITree (Effect)

/-! ## Expression and control equations -/

theorem source_raw_exp_plus {X : Type} (ea eb : CExp) (K : Nat → CTree CEff Bn X) :
    (denote_exp (.plus ea eb) >>= K) =
      (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)) := by
  simp only [denote_exp, bind_assoc, pure_bind']

theorem source_raw_exp_minus {X : Type} (ea eb : CExp) (K : Nat → CTree CEff Bn X) :
    (denote_exp (.minus ea eb) >>= K) =
      (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)) := by
  simp only [denote_exp, bind_assoc, pure_bind']

theorem source_raw_exp_mult {X : Type} (ea eb : CExp) (K : Nat → CTree CEff Bn X) :
    (denote_exp (.mult ea eb) >>= K) =
      (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)) := by
  simp only [denote_exp, bind_assoc, pure_bind']

/-- The one-unroll equation preserves expression evaluation and the actual source continuation,
including halt and guarded loop re-entry. -/
theorem source_raw_while_unfold (test : CExp) (body : CProg Unit)
    (K : Option Unit → Thread sE Bn) :
    (denote_flow (.while test body) >>= K) =
      (denote_exp test >>= fun value =>
        if is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | none => K none
            | some _ => .guard (denote_flow (.while test body) >>= K)
        else K (some ())) := by
  conv => lhs; rw [source_raw_while, unfold_iter]
  rw [denote_flow_cwhile]
  simp only [cwhile_iteration, bind_assoc]
  congr 1; funext value
  cases is_true value
  · simp
  · simp only [↓reduceIte, bind_assoc]
    congr 1; funext flow
    cases flow <;> simp

/-! ## Focused equations under the nondeterministic runner -/

theorem interp_nd_source_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (e : CExp)
    (K : Option Nat → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.eval e) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1) (ts.set i (denote_exp e >>= fun value => K (some value)))
        (some i) σ := by
  rw [source_raw_eval]

theorem interp_nd_source_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (some i) σ := by
  rw [source_raw_if]

theorem interp_nd_source_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)))
        (some i) σ := by
  rw [source_raw_exp_plus]

theorem interp_nd_source_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)))
        (some i) σ := by
  rw [source_raw_exp_minus]

theorem interp_nd_source_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)))
        (some i) σ := by
  rw [source_raw_exp_mult]

/-- The raw allocation head with the handler response left unresolved. -/
private theorem interp_nd_alloc_head (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) σ ~
      (heap_handlerW CSLObs.heap (.alloc size) σ >>= fun p =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some p.1))) (some i) p.2) := by
  refine sbisim_trans (interp_schedule_nd_user_bind sh n ts i _ (.inl (.alloc size))
    (fun x => K (some x)) σ (source_raw_alloc_head size K)) ?_
  rw [interp_state_trigger, bind_assoc]
  exact sbisim_bind_eq _ fun _ => by simp only [guard_bind, pure_bind']; exact sb_guard _

theorem interp_nd_source_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  refine sbisim_trans (interp_nd_alloc_head n ts i 0 K _) ?_
  rw [heap_handlerW_alloc_zero, stuck_bind]
  exact sbisim_refl _

theorem interp_nd_source_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (CTree.spin : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  intro Pos Full
  refine sbisim_trans (interp_nd_alloc_head n ts i size K _) ?_
  rw [heap_handlerW_alloc_no_space _ h allocs size _ Pos Full, spin_bind]
  exact sbisim_refl _

theorem interp_nd_source_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (.guard t)) (some i) σ ~
      interp_schedule_nd sh (n + 1) (ts.set i t) (some i) σ := by
  have := interp_schedule_nd_guard sh n (ts.set i (.guard t)) i t σ (by simp)
  rwa [Vector.set_set] at this

theorem interp_nd_source_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.while test body) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then
            denote_flow body >>= fun flow =>
              match flow with
              | none => K none
              | some _ => .guard (denote_flow (.while test body) >>= K)
          else K (some ()))) (some i) σ :=
  congrArg (fun t => interp_schedule_nd sh (n + 1) (ts.set i t) (some i) σ)
    (source_raw_while_unfold test body K)

/-! ## Focused equations under a scheduling policy -/

section FairKernel
variable (sch : Scheduler)

theorem interp_fair_source_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (e : CExp) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.eval e) >>= K)) (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => K (some value))) (some i) st σ := by
  rw [source_raw_eval]

theorem interp_fair_source_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (st : sch.sched_state)
    (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K))
        (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then denote_flow yes >>= K else denote_flow no >>= K))
        (some i) st σ := by
  rw [source_raw_if]

theorem interp_fair_source_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K)) (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)))
        (some i) st σ := by
  rw [source_raw_exp_plus]

theorem interp_fair_source_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K))
        (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)))
        (some i) st σ := by
  rw [source_raw_exp_minus]

theorem interp_fair_source_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K)) (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)))
        (some i) st σ := by
  rw [source_raw_exp_mult]

theorem interp_fair_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [source_raw_alloc_head]
  refine sbisim_trans (interp_schedule_fair_user_bind sch sh n ts i _ (.inl (.alloc 0))
    (fun x => K (some x)) st _ rfl) ?_
  show translate relabel_log (heap_handlerW CSLObs.heap (.alloc 0) ((h, allocs), (ctx, c))) >>=
    _ ~ _
  rw [heap_handlerW_alloc_zero, translate_stuck_node, stuck_bind]
  exact sbisim_refl _

theorem interp_fair_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (CTree.spin : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  intro Pos Full
  rw [source_raw_alloc_head]
  refine sbisim_trans (interp_schedule_fair_user_bind sch sh n ts i _ (.inl (.alloc size))
    (fun x => K (some x)) st _ rfl) ?_
  show translate relabel_log
    (heap_handlerW CSLObs.heap (.alloc size) ((h, allocs), (ctx, c))) >>= _ ~ _
  rw [heap_handlerW_alloc_no_space _ h allocs size _ Pos Full, translate_spin, spin_bind]
  exact sbisim_refl _

theorem interp_fair_source_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (.guard t)) (some i) st σ ~
      interp_schedule_fair sch sh (n + 1) (ts.set i t) (some i) st σ := by
  have := interp_schedule_fair_guard sch sh n (ts.set i (.guard t)) i t st σ (by simp)
  rwa [Vector.set_set] at this

theorem interp_fair_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.while test body) >>= K))
        (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then
            denote_flow body >>= fun flow =>
              match flow with
              | none => K none
              | some _ => .guard (denote_flow (.while test body) >>= K)
          else K (some ()))) (some i) st σ :=
  congrArg (fun t => interp_schedule_fair sch sh (n + 1) (ts.set i t) (some i) st σ)
    (source_raw_while_unfold test body K)

end FairKernel

/-! ## Round robin: the `rr_scheduler` instances -/

theorem interp_rr_source_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (e : CExp)
    (K : Option Nat → Thread sE Bn) (cursor : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.eval e) >>= K)) (some i) cursor σ =
      interp_schedule_rr sh (n + 1) (ts.set i (denote_exp e >>= fun value => K (some value)))
        (some i) cursor σ :=
  interp_fair_source_eval rr_scheduler n ts i e K cursor σ

theorem interp_rr_source_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (cursor : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i)
        cursor σ =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then denote_flow yes >>= K else denote_flow no >>= K))
        (some i) cursor σ :=
  interp_fair_source_if rr_scheduler n ts i test yes no K cursor σ

theorem interp_rr_source_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (cursor : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K)) (some i) cursor σ =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)))
        (some i) cursor σ :=
  interp_fair_source_exp_plus rr_scheduler n ts i ea eb K cursor σ

theorem interp_rr_source_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (cursor : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) cursor σ =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)))
        (some i) cursor σ :=
  interp_fair_source_exp_minus rr_scheduler n ts i ea eb K cursor σ

theorem interp_rr_source_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (cursor : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K)) (some i) cursor σ =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)))
        (some i) cursor σ :=
  interp_fair_source_exp_mult rr_scheduler n ts i ea eb K cursor σ

theorem interp_rr_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (cursor : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K)) (some i) cursor
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_fair_alloc_zero rr_scheduler n ts i K cursor h allocs ctx c

theorem interp_rr_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (cursor : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) cursor
        ((h, allocs), (ctx, c)) ~
      (CTree.spin : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_fair_alloc_no_space rr_scheduler n ts i size K cursor h allocs ctx c

theorem interp_rr_source_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread sE Bn) (cursor : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (.guard t)) (some i) cursor σ ~
      interp_schedule_rr sh (n + 1) (ts.set i t) (some i) cursor σ :=
  interp_fair_source_guard rr_scheduler n ts i t cursor σ

theorem interp_rr_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (cursor : Nat)
    (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.while test body) >>= K))
        (some i) cursor σ =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then
            denote_flow body >>= fun flow =>
              match flow with
              | none => K none
              | some _ => .guard (denote_flow (.while test body) >>= K)
          else K (some ()))) (some i) cursor σ :=
  interp_fair_while_unfold rr_scheduler n ts i test body K cursor σ

/-! ## Observable emission and cooperative selection -/

section Temporal
local notation "WN" => writerE (CSLObs (Nat × Nat))
local notation "WR" => writerE (CSLObs (Nat × Nat) ⊕ Nat)
variable {b : Option Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))

section ND

theorem an_csl_nd_emit (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) (ψ : Ticl WN b) :
    entails (φ AN ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails φ (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1))) w ∧
      entails ψ (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1)))
        (.obs (E := WN) (CSLObs.emit (stamp (tag, value) c)) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_nd_source_emit_log n ts i tag value K memory ctx c)]
  exact an_log_iff

theorem au_csl_nd_emit (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) (ψ : Ticl WN b) :
    entails (φ AU ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails ψ (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1))) w ∨
      entails φ (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1))) w ∧
      entails (φ AU ψ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1)))
        (.obs (E := WN) (CSLObs.emit (stamp (tag, value) c)) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_nd_source_emit_log n ts i tag value K memory ctx c)]
  exact au_log_iff

theorem ag_csl_nd_emit (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (AG φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails φ (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1))) w ∧
      entails (AG φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1)))
        (.obs (E := WN) (CSLObs.emit (stamp (tag, value) c)) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_nd_source_emit_log n ts i tag value K memory ctx c)]
  exact ag_log_iff

theorem an_csl_nd_yield (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) (ψ : Ticl WN b) :
    entails (φ AN ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow .yield >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∧
      ∀ j : Fin (n + 1),
        entails ψ (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j)
          (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_nd_source_yield n ts i K _)]
  exact an_csl_nd_select n memory ctx c _ w φ ψ

theorem au_csl_nd_yield (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) (ψ : Ticl WN b) :
    entails (φ AU ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow .yield >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails ψ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∨
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∧
      ∀ j : Fin (n + 1),
        entails (φ AU ψ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j)
          (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_nd_source_yield n ts i K _)]
  exact au_csl_nd_select n memory ctx c _ w φ ψ

theorem ag_csl_nd_yield (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (AG φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow .yield >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∧
      ∀ j : Fin (n + 1),
        entails (AG φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j)
          (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_nd_source_yield n ts i K _)]
  exact ag_csl_nd_select n memory ctx c _ w φ

end ND

section RR

theorem an_csl_rr_emit (tag value : Nat) (K : Option Unit → Thread sE Bn) (m : Nat)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR b) :
    entails (φ AN ψ) (interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) m (memory, (ctx, c))) w ↔
      entails φ (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat × Nat) ⊕ Nat) >>=
        fun _ => interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1))) w ∧
      entails ψ (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1)))
        (.obs (E := WR) (.inl (CSLObs.emit (stamp (tag, value) c))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_rr_emit_log n ts i tag value K m memory ctx c)]
  exact an_log_iff

theorem au_csl_rr_emit (tag value : Nat) (K : Option Unit → Thread sE Bn) (m : Nat)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR b) :
    entails (φ AU ψ) (interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) m (memory, (ctx, c))) w ↔
      entails ψ (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat × Nat) ⊕ Nat) >>=
        fun _ => interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1))) w ∨
      entails φ (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat × Nat) ⊕ Nat) >>=
        fun _ => interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1))) w ∧
      entails (φ AU ψ) (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1)))
        (.obs (E := WR) (.inl (CSLObs.emit (stamp (tag, value) c))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_rr_emit_log n ts i tag value K m memory ctx c)]
  exact au_log_iff

theorem ag_csl_rr_emit (tag value : Nat) (K : Option Unit → Thread sE Bn) (m : Nat)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) m (memory, (ctx, c))) w ↔
      entails φ (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat × Nat) ⊕ Nat) >>=
        fun _ => interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1))) w ∧
      entails (AG φ) (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1)))
        (.obs (E := WR) (.inl (CSLObs.emit (stamp (tag, value) c))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_rr_emit_log n ts i tag value K m memory ctx c)]
  exact ag_log_iff

/-! A round-robin yield logs the scheduler's selected slot before the picked slot runs: the
shapes mirror `an_csl_rr_select`, `au_csl_rr_select` and `ag_csl_rr_select`. -/

theorem an_csl_rr_yield (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR b) :
    entails (φ AN ψ) (interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow .yield >>= K)) (some i) m (memory, (ctx, c))) w ↔
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1)
          (memory, (ctx, c))) w ∧
      entails ψ (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some (rr_pick n m))
          (m + 1) (memory, (ctx, c)))
        (.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_rr_yield n ts i K m _)]
  exact an_csl_rr_select n memory ctx c _ m w φ ψ

theorem au_csl_rr_yield (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR b) :
    entails (φ AU ψ) (interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow .yield >>= K)) (some i) m (memory, (ctx, c))) w ↔
      entails ψ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1)
          (memory, (ctx, c))) w ∨
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1)
          (memory, (ctx, c))) w ∧
      entails (φ AU ψ) (interp_schedule_rr sh (n + 1) (ts.set i (K (some ())))
          (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_rr_yield n ts i K m _)]
  exact au_csl_rr_select n memory ctx c _ m w φ ψ

theorem ag_csl_rr_yield (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow .yield >>= K)) (some i) m (memory, (ctx, c))) w ↔
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1)
          (memory, (ctx, c))) w ∧
      entails (AG φ) (interp_schedule_rr sh (n + 1) (ts.set i (K (some ())))
          (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_rr_yield n ts i K m _)]
  exact ag_csl_rr_select n memory ctx c _ m w φ

end RR

/-! ## Finite heaps supply their constructive first-fit witness -/

theorem ticl_csl_nd_alloc_finite (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WN) (p : Ticl WN b) :
    heap_finite h → 0 < size → NotDone w →
    (entails p (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      ∀ base, 0 < base → block_free h base size →
        (∀ j, 0 < j → j < base → ¬ block_free h j size) →
        entails p (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat))
          >>= fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c))) w) := by
  intro Finite Pos _
  exact first_fit_iff Finite Pos fun base Base Free First => proper_entails_meq p
    (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First)

theorem ticl_csl_rr_alloc_finite (size : Nat) (K : Option Nat → Thread sE Bn) (m : Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (p : Ticl WR b) :
    heap_finite h → 0 < size → NotDone w →
    (entails p (interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) m ((h, allocs), (ctx, c))) w ↔
      ∀ base, 0 < base → block_free h base size →
        (∀ j, 0 < j → j < base → ¬ block_free h j size) →
        entails p (log (.inl (CSLObs.heap (managed_alloc (h, allocs) base size)) :
            CSLObs (Nat × Nat) ⊕ Nat)
          >>= fun _ => interp_schedule_rr sh (n + 1) (ts.set i (K (some base))) (some i) m
            (managed_alloc (h, allocs) base size, (ctx, c))) w) := by
  intro Finite Pos _
  exact first_fit_iff Finite Pos fun base Base Free First => proper_entails_meq p
    (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First)

end Temporal

-- Not ported: nothing. Every Rocq declaration of lines 1684-2204 is above (the ND/RR
-- `interp_*` equations additionally get a policy-generic `interp_fair_*` kernel; RR emit and
-- yield rules are proved directly from `interp_rr_emit_log`/`interp_rr_yield`).

end CoCSL
