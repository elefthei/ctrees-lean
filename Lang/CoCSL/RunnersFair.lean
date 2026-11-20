/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Runners

/-!
# CoCSL focused instruction equations under a scheduling policy

The policy-generic kernel: every focused source instruction rewritten under
`interp_schedule_fair sch sh` for an arbitrary `sch : Scheduler`, together with the round-robin
names `interp_rr_*` as its `rr_scheduler` instances, and the fork-headed startup of the
singleton runners (← `Lang/CoCSL/Mod.v`, lines 560-1494, policy and round-robin family).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx
open ITree (Effect)

/-! ## The policy-generic kernel -/

section FairKernel
variable (sch : Scheduler)

/-- A literal is pure. -/
theorem interp_fair_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (v : Nat)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (s : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_exp (.lit v) >>= K)) (some i) st s =
      interp_schedule_fair sch sh (n + 1) (ts.set i (K v)) (some i) st s := by
  rw [source_raw_lit]

/-- Assignment evaluates its expression, then performs a late read-modify-write of the shared
context. -/
theorem interp_fair_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (e : CExp) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (s : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.assign name e) >>= K))
        (some i) st s =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp e >>= fun value =>
          source_get >>= fun ctx => source_put (Ctx.add name value ctx) >>= fun _ => K (some ())))
        (some i) st s := by
  rw [source_raw_assign]

/-- Expression CAS evaluates its operands inside the focused thread, keeping every yield, before
the literal heap operation. -/
theorem interp_fair_cas_exp (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (s : SSig) :
    interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i) st s =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_exp a >>= fun addr => denote_exp expected >>= fun old =>
          denote_exp desired >>= fun value =>
          denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K)) (some i) st s := by
  rw [source_raw_cas]

theorem interp_fair_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (value : Nat) (K : Nat → Thread sE Bn) (st : sch.sched_state) (s : SSig) :
    Ctx.lookup name (csl_context s) = some value →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_exp (.var name) >>= K)) (some i) st s ~
      interp_schedule_fair sch sh (n + 1) (ts.set i (K value)) none st s := by
  grind

/-- A missing variable makes the whole run stuck. -/
theorem interp_fair_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (st : sch.sched_state) (s : SSig) :
    Ctx.lookup name (csl_context s) = none →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_exp (.var name) >>= K)) (some i) st s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  grind

theorem interp_fair_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (x : A)
    (K : Option A → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) st σ =
      interp_schedule_fair sch sh (n + 1) (ts.set i (K (some x))) (some i) st σ := by
  rw [source_raw_ret]

theorem interp_fair_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) st σ ~
      (translate relabel_log (interp_state sh (heap_read (E := sE) (B := Bn) a) σ) >>= fun p =>
        interp_schedule_fair sch sh (n + 1) (ts.set i (K (some p.1))) (some i) st p.2) := by
  rw [source_raw_read_head]
  exact sbisim_trans (interp_schedule_fair_user_bind sch sh n ts i _ (.inl (.read a))
    (fun x => K (some x)) st σ rfl)
    (sbisim_symm (translate_interp_state_trigger_bind sh (.inl (.read a)) _ σ))

theorem interp_fair_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) st σ ~
      (translate relabel_log (interp_state sh (heap_alloc (E := sE) (B := Bn) size) σ) >>=
        fun p => interp_schedule_fair sch sh (n + 1) (ts.set i (K (some p.1))) (some i) st p.2) :=
    by
  rw [source_raw_alloc_head]
  exact sbisim_trans (interp_schedule_fair_user_bind sch sh n ts i _ (.inl (.alloc size))
    (fun x => K (some x)) st σ rfl)
    (sbisim_symm (translate_interp_state_trigger_bind sh (.inl (.alloc size)) _ σ))

theorem interp_fair_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (σ : SSig) :
    interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K))
        (some i) st σ ~
      (translate relabel_log
          (interp_state sh (heap_cas (E := sE) (B := Bn) a expected desired) σ) >>=
        fun p => interp_schedule_fair sch sh (n + 1) (ts.set i (K (some p.1))) (some i) st p.2) :=
    by
  rw [source_raw_cas_head]
  exact sbisim_trans (interp_schedule_fair_user_bind sch sh n ts i _
    (.inl (.cas a expected desired)) (fun x => K (some x)) st σ rfl)
    (sbisim_symm (translate_interp_state_trigger_bind sh (.inl (.cas a expected desired)) _ σ))

theorem interp_fair_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a v : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K))
        (some i) st σ ~
      (translate relabel_log (interp_state sh (heap_write (E := sE) (B := Bn) a v) σ) >>=
        fun p => interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st p.2) := by
  rw [source_raw_write_head]
  exact sbisim_trans (interp_schedule_fair_user_bind sch sh n ts i _ (.inl (.write a v))
    (fun _ => K (some ())) st σ rfl)
    (sbisim_symm (translate_interp_state_trigger_bind sh (.inl (.write a v)) _ σ))

theorem interp_fair_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (q v : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.emit q v) >>= K))
        (some i) st σ ~
      (translate relabel_log (interp_state sh (semit q v) σ) >>=
        fun p => interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st p.2) := by
  rw [source_raw_emit_head]
  exact sbisim_trans (interp_schedule_fair_user_bind sch sh n ts i _ (.inr (.inr (q, v)))
    (fun _ => K (some ())) st σ rfl)
    (sbisim_symm (translate_interp_state_trigger_bind sh (.inr (.inr (q, v))) _ σ))

theorem interp_fair_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (st : sch.sched_state)
    (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.bind p next) >>= K))
        (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_flow p >>= fun r =>
          match r with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) st σ := by
  exact congrArg (fun t => interp_schedule_fair sch sh (n + 1) (ts.set i t) (some i) st σ)
    ((source_raw_bind p next K).trans rfl)

/-- Yield replaces the focused thread by its continuation and clears the focus. -/
theorem interp_fair_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow .yield >>= K)) (some i) st σ ~
      interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) none st σ := by
  grind

/-- Fork prepends the child, replaces the parent by its continuation and keeps the parent
focused at its shifted slot. -/
theorem interp_fair_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (p : CProg Unit)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.fork p) >>= K)) (some i) st σ ~
      interp_schedule_fair sch sh (n + 2)
        (Vector.cons (denote_flow p >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) st σ := by
  grind

theorem interp_fair_until_none {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (σ : SSig) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K))
        (some i) st σ =
      interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_flow body >>= fun r =>
          match r with
          | none => K none
          | some none => K (some ())
          | some (some _) => .guard (denote_flow (.untilNone body) >>= K)))
        (some i) st σ := by
  exact congrArg (fun t => interp_schedule_fair sch sh (n + 1) (ts.set i t) (some i) st σ)
    ((source_raw_until body K).trans rfl)

/-! ### Handler-resolved equations -/

/-- A successful checked write exposes its post-operation memory before continuing at the same
focus. -/
theorem interp_fair_write_present (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a v : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    h a ≠ none →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (log (.inl (CSLObs.heap (upd h a v, allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          ((upd h a v, allocs), (ctx, c))) := by
  grind

theorem interp_fair_read_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    h a = some value →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      interp_schedule_fair sch sh (n + 1) (ts.set i (K (some value))) (some i) st
        ((h, allocs), (ctx, c)) := by
  grind

/-- Emission logs `CSLEmit (stamp (tag, value) c)` and advances the counter. -/
theorem interp_fair_emit_log (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (tag value : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K)) (some i)
        st (memory, (ctx, c)) ~
      (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          (memory, (ctx, c + 1))) := by
  grind

/-- Literal CAS: success logs the updated memory and returns `true`; failure is silent. -/
theorem interp_fair_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a = some current →
    interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (if current = expected then
        log (.inl (CSLObs.heap (upd h a desired, allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
          interp_schedule_fair sch sh (n + 1) (ts.set i (K (some true))) (some i) st
            ((upd h a desired, allocs), (ctx, c))
      else
        interp_schedule_fair sch sh (n + 1) (ts.set i (K (some false))) (some i) st
          ((h, allocs), (ctx, c))) := by
  grind

/-- First-fit allocation logs the new managed memory and returns the first free base. -/
theorem interp_fair_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (log (.inl (CSLObs.heap (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat)
        >>= fun _ =>
        interp_schedule_fair sch sh (n + 1) (ts.set i (K (some base))) (some i) st
          (managed_alloc (h, allocs) base size, (ctx, c))) := by
  intro Pos Base Free First
  grind [sh_alloc_first h allocs size base (ctx, c) Pos Base Free First]

theorem interp_fair_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    h a = none →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  grind

theorem interp_fair_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a v : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    h a = none →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  grind

theorem interp_fair_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a = none →
    interp_schedule_fair sch sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i) st
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  grind

/-- Whole-block free keeps the focus: nonzero success logs the released memory, free zero is
silent. -/
theorem interp_fair_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory memory' : ManagedHeap)
    (ctx : Ctx) (c : Nat) :
    managed_free memory base = some memory' →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.free base) >>= K)) (some i) st
        (memory, (ctx, c)) ~
      match base with
      | 0 => interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          (memory', (ctx, c))
      | _ + 1 =>
        log (.inl (CSLObs.heap memory') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
          interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
            (memory', (ctx, c)) := by
  intro Free
  cases base <;> grind

/-- Interior-pointer, unknown-base and double frees fault. -/
theorem interp_fair_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) :
    managed_free memory base = none →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (.free base) >>= K)) (some i) st
        (memory, (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  grind

/-- A fork-headed singleton starts as a two-slot pool, child first, with the parent focused. -/
theorem run_fair_fork_bind (p : CProg Unit) (next : Unit → CProg Unit) (st : sch.sched_state)
    (s : SSig) :
    run_fair sch (.bind (.fork p) next) st s ~
      interp_schedule_fair sch sh 2 #v[denote p, denote (next ())] (some 1) st s := by
  rw [run_fair_unfold]
  refine sbisim_trans (interp_schedule_fair_fork sch sh 0 _ 0
    (fun child : Bool => if child then denote p else denote (next ())) st s
    (by show (denote (.bind (.fork p) next)).unfold = _; rw [denote_fork_bind]; simp)) ?_
  exact sbisim_refl _

end FairKernel

/-! ## Round robin: the `rr_scheduler` instances -/

section RoundRobin

theorem interp_rr_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (v : Nat)
    (K : Nat → Thread sE Bn) (m : Nat) (s : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_exp (.lit v) >>= K)) (some i) m s =
      interp_schedule_rr sh (n + 1) (ts.set i (K v)) (some i) m s :=
  interp_fair_lit rr_scheduler n ts i v K m s

theorem interp_rr_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (e : CExp) (K : Option Unit → Thread sE Bn) (m : Nat) (s : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.assign name e) >>= K)) (some i) m s =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_exp e >>= fun value =>
          source_get >>= fun ctx => source_put (Ctx.add name value ctx) >>= fun _ => K (some ())))
        (some i) m s :=
  interp_fair_assign rr_scheduler n ts i name e K m s

theorem interp_rr_cas_exp (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (m : Nat) (s : SSig) :
    interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i) m s =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_exp a >>= fun addr => denote_exp expected >>= fun old =>
          denote_exp desired >>= fun value =>
          denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K)) (some i) m s :=
  interp_fair_cas_exp rr_scheduler n ts i a expected desired K m s

theorem interp_rr_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (value : Nat) (K : Nat → Thread sE Bn) (m : Nat) (s : SSig) :
    Ctx.lookup name (csl_context s) = some value →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_exp (.var name) >>= K)) (some i) m s ~
      interp_schedule_rr sh (n + 1) (ts.set i (K value)) none m s :=
  interp_fair_var rr_scheduler n ts i name value K m s

theorem interp_rr_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (m : Nat) (s : SSig) :
    Ctx.lookup name (csl_context s) = none →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_exp (.var name) >>= K)) (some i) m s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_fair_var_missing rr_scheduler n ts i name K m s

theorem interp_rr_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (x : A)
    (K : Option A → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) m σ =
      interp_schedule_rr sh (n + 1) (ts.set i (K (some x))) (some i) m σ :=
  interp_fair_ret rr_scheduler n ts i x K m σ

theorem interp_rr_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) m σ ~
      (translate relabel_log (interp_state sh (heap_read (E := sE) (B := Bn) a) σ) >>= fun p =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some p.1))) (some i) m p.2) :=
  interp_fair_read rr_scheduler n ts i a K m σ

theorem interp_rr_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size : Nat)
    (K : Option Nat → Thread sE Bn) (m : Nat) (sigma : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) m sigma ~
      (translate relabel_log (interp_state sh (heap_alloc (E := sE) (B := Bn) size) sigma) >>=
        fun p => interp_schedule_rr sh (n + 1) (ts.set i (K (some p.1))) (some i) m p.2) :=
  interp_fair_alloc rr_scheduler n ts i size K m sigma

theorem interp_rr_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (m : Nat) (sigma : SSig) :
    interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K))
        (some i) m sigma ~
      (translate relabel_log
          (interp_state sh (heap_cas (E := sE) (B := Bn) a expected desired) sigma) >>=
        fun p => interp_schedule_rr sh (n + 1) (ts.set i (K (some p.1))) (some i) m p.2) :=
  interp_fair_cas rr_scheduler n ts i a expected desired K m sigma

theorem interp_rr_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a v : Nat)
    (K : Option Unit → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i) m σ ~
      (translate relabel_log (interp_state sh (heap_write (E := sE) (B := Bn) a v) σ) >>=
        fun p => interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m p.2) :=
  interp_fair_write rr_scheduler n ts i a v K m σ

theorem interp_rr_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (q v : Nat)
    (K : Option Unit → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.emit q v) >>= K)) (some i) m σ ~
      (translate relabel_log (interp_state sh (semit q v) σ) >>=
        fun p => interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m p.2) :=
  interp_fair_emit rr_scheduler n ts i q v K m σ

theorem interp_rr_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) m σ =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow p >>= fun r =>
          match r with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) m σ :=
  interp_fair_bind rr_scheduler n ts i p next K m σ

theorem interp_rr_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow .yield >>= K)) (some i) m σ ~
      interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) none m σ :=
  interp_fair_yield rr_scheduler n ts i K m σ

theorem interp_rr_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (p : CProg Unit)
    (K : Option Unit → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.fork p) >>= K)) (some i) m σ ~
      interp_schedule_rr sh (n + 2)
        (Vector.cons (denote_flow p >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) m σ :=
  interp_fair_fork rr_scheduler n ts i p K m σ

theorem interp_rr_until_none {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn) (m : Nat) (σ : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) m σ =
      interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow body >>= fun r =>
          match r with
          | none => K none
          | some none => K (some ())
          | some (some _) => .guard (denote_flow (.untilNone body) >>= K)))
        (some i) m σ :=
  interp_fair_until_none rr_scheduler n ts i body K m σ

theorem run_rr_fork_bind (p : CProg Unit) (next : Unit → CProg Unit) (s : SSig) :
    run_rr (.bind (.fork p) next) s ~
      interp_schedule_rr sh 2 #v[denote p, denote (next ())] (some 1) 0 s :=
  run_fair_fork_bind rr_scheduler p next (0 : Nat) s

theorem interp_rr_write_present (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a v : Nat) (K : Option Unit → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    h a ≠ none →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      (log (.inl (CSLObs.heap (upd h a v, allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          ((upd h a v, allocs), (ctx, c))) :=
  interp_fair_write_present rr_scheduler n ts i a v K m h allocs ctx c

theorem interp_rr_read_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    h a = some value →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      interp_schedule_rr sh (n + 1) (ts.set i (K (some value))) (some i) m
        ((h, allocs), (ctx, c)) :=
  interp_fair_read_value rr_scheduler n ts i a value K m h allocs ctx c

theorem interp_rr_emit_log (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (tag value : Nat) (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) m
        (memory, (ctx, c)) ~
      (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          (memory, (ctx, c + 1))) :=
  interp_fair_emit_log rr_scheduler n ts i tag value K m memory ctx c

theorem interp_rr_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (m : Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a = some current →
    interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      (if current = expected then
        log (.inl (CSLObs.heap (upd h a desired, allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
          interp_schedule_rr sh (n + 1) (ts.set i (K (some true))) (some i) m
            ((upd h a desired, allocs), (ctx, c))
      else
        interp_schedule_rr sh (n + 1) (ts.set i (K (some false))) (some i) m
          ((h, allocs), (ctx, c))) :=
  interp_fair_cas_value rr_scheduler n ts i a expected desired current K m h allocs ctx c

theorem interp_rr_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      (log (.inl (CSLObs.heap (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat)
        >>= fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some base))) (some i) m
          (managed_alloc (h, allocs) base size, (ctx, c))) :=
  interp_fair_alloc_first rr_scheduler n ts i size base K m h allocs ctx c

theorem interp_rr_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a = none →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_fair_read_missing rr_scheduler n ts i a K m h allocs ctx c

theorem interp_rr_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a v : Nat) (K : Option Unit → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    h a = none →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_fair_write_missing rr_scheduler n ts i a v K m h allocs ctx c

theorem interp_rr_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (m : Nat) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    h a = none →
    interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_fair_cas_missing rr_scheduler n ts i a expected desired K m h allocs ctx c

theorem interp_rr_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (cursor : Nat) (memory memory' : ManagedHeap) (ctx : Ctx)
    (c : Nat) :
    managed_free memory base = some memory' →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.free base) >>= K)) (some i) cursor
        (memory, (ctx, c)) ~
      match base with
      | 0 => interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) cursor
          (memory', (ctx, c))
      | _ + 1 =>
        log (.inl (CSLObs.heap memory') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
          interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) cursor
            (memory', (ctx, c)) :=
  interp_fair_free rr_scheduler n ts i base K cursor memory memory' ctx c

theorem interp_rr_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (cursor : Nat) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) :
    managed_free memory base = none →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.free base) >>= K)) (some i) cursor
        (memory, (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_fair_free_invalid rr_scheduler n ts i base K cursor memory ctx c

end RoundRobin

-- Not ported here (by design of the CoCSL split): the ND runner equations
-- `interp_nd_*`/`interp_nd_source_*`, the runner defs, `run_*_unfold`, `source_raw_{lit,var}`,
-- `first_fit_exists` and `source_free_raw_heap_free` live in `Lang/CoCSL/Runners.lean`
-- (same Rocq range); the Ltac `csl_lift_handler_result` has no Lean counterpart.

end CoCSL
