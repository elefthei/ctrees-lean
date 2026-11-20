/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Syntax
public import Logic.Sep.CSL
public import Logic.Yield.Nondeterministic
public import Logic.Yield.RoundRobin
public import Logic.Yield.Policy
public import Logic.Yield.Segments

/-!
# CoCSL runners

A pool of source programs runs under the nondeterministic, round-robin or a generic policy
scheduler from an explicit full state `((h, allocs), (ctx, c))`; the singleton runners start
focused (round robin at cursor `0`). Focused instruction equations of the ND runner,
handler-resolved equations and exact first-yield segments (← `Lang/CoCSL/Mod.v`, lines 489-1683,
minus the policy family in `Lang/CoCSL/RunnersFair.lean`).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield
open ITree (Effect)

/-! ## Runners -/

def csl_pool {n : Nat} (ps : Vector (CProg Unit) n) : Pool sE Bn n :=
  ps.map denote

def run_nd_pool {n : Nat} (ps : Vector (CProg Unit) n) (focus : Option (Fin n)) (s : SSig) :
    ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig) :=
  interp_schedule_nd sh n (csl_pool ps) focus s

def run_rr_pool {n : Nat} (ps : Vector (CProg Unit) n) (focus : Option (Fin n)) (cursor : Nat)
    (s : SSig) : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig) :=
  interp_schedule_rr sh n (csl_pool ps) focus cursor s

def run_nd (p : CProg Unit) (s : SSig) : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig) :=
  run_nd_pool #v[p] (some 0) s

def run_rr (p : CProg Unit) (s : SSig) : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig) :=
  run_rr_pool #v[p] (some 0) 0 s

/-- Derived recurrence of payload-emission edges for every initial counter. -/
def run_rr_recurrently_emits (p : CProg Unit) (memory : ManagedHeap) (ctx : Ctx)
    (P : Nat × Nat → Prop) : Prop :=
  ∀ c, RecurrentLabel (csl_label_emitsW P) (run_rr p (memory, (ctx, c)))

/-- The scheduler-generic instrumented runner: picks logged as `.inr slot`, program
observations relabelled `.inl`. -/
def run_fair_pool (sch : Scheduler) {n : Nat} (ps : Vector (CProg Unit) n)
    (focus : Option (Fin n)) (st : sch.sched_state) (s : SSig) :
    ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig) :=
  interp_schedule_fair sch sh n (csl_pool ps) focus st s

def run_fair (sch : Scheduler) (p : CProg Unit) (st : sch.sched_state) (s : SSig) :
    ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig) :=
  run_fair_pool sch #v[p] (some 0) st s

theorem run_nd_unfold (p : CProg Unit) (s : SSig) :
    run_nd p s = interp_schedule_nd sh 1 #v[denote p] (some 0) s := by
  simp [run_nd, run_nd_pool, csl_pool]

theorem run_rr_unfold (p : CProg Unit) (s : SSig) :
    run_rr p s = interp_schedule_rr sh 1 #v[denote p] (some 0) 0 s := by
  simp [run_rr, run_rr_pool, csl_pool]

theorem run_fair_unfold (sch : Scheduler) (p : CProg Unit) (st : sch.sched_state) (s : SSig) :
    run_fair sch p st s = interp_schedule_fair sch sh 1 #v[denote p] (some 0) st s := by
  simp [run_fair, run_fair_pool, csl_pool]

/-- A singleton ND run as an explicit replacement of its only slot. -/
theorem run_nd_focus (p : CProg Unit) (s : SSig) :
    run_nd p s = interp_schedule_nd sh 1 ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1)
      (denote_flow p >>= fun _ => pure ⟨⟩)) (some 0) s := by
  rw [run_nd_unfold]; rfl

/-- A singleton RR run as an explicit replacement of its only slot. -/
theorem run_rr_focus (p : CProg Unit) (s : SSig) :
    run_rr p s = interp_schedule_rr sh 1 ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1)
      (denote_flow p >>= fun _ => pure ⟨⟩)) (some 0) 0 s := by
  rw [run_rr_unfold]; rfl

/-- The source pool of a literal pair is the literal pair of denotations (`Vector.map` on a
literal does not reduce definitionally). -/
theorem csl_pool_pair (p q : CProg Unit) : csl_pool #v[p, q] = #v[denote p, denote q] := by
  simp [csl_pool]

/-! ## Expression execution

A literal is pure. A variable reads the shared context and on success yields once before
returning the captured value; a missing variable is stuck, faulting the whole run. -/

theorem source_raw_lit {X : Type} (n : Nat) (K : Nat → CTree CEff Bn X) :
    (denote_exp (.lit n) >>= K) = K n := by
  simp [denote_exp]

@[grind =] theorem source_raw_var {X : Type} (name : String) (K : Nat → CTree CEff Bn X) :
    (denote_exp (.var name) >>= K) =
      (source_get >>= fun ctx =>
        match Ctx.lookup name ctx with
        | some value => .vis (E := CEff) (.inl ⟨⟩) fun _ => K value
        | none => .stuck) := by
  rw [denote_exp, bind_assoc]
  congr 1; funext ctx
  cases Ctx.lookup name ctx <;> simp [source_yield]

theorem interp_nd_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (v : Nat)
    (K : Nat → Thread sE Bn) (s : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.lit v) >>= K)) (some i) s =
      interp_schedule_nd sh (n + 1) (ts.set i (K v)) (some i) s := by
  rw [source_raw_lit]

/-- Assignment evaluates its expression, then performs a late read-modify-write of the shared
context. -/
theorem interp_nd_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (e : CExp) (K : Option Unit → Thread sE Bn) (s : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.assign name e) >>= K)) (some i) s =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value =>
          source_get >>= fun ctx => source_put (Ctx.add name value ctx) >>= fun _ =>
            K (some ())))
        (some i) s := by
  rw [source_raw_assign]

/-- Expand expression CAS inside the focused thread, retaining every yield before the literal
heap operation. -/
theorem interp_nd_cas_exp (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (s : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.cas a expected desired) >>= K))
        (some i) s =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp a >>= fun addr => denote_exp expected >>= fun old =>
          denote_exp desired >>= fun value =>
            denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K))
        (some i) s := by
  rw [source_raw_cas]

theorem interp_nd_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (value : Nat) (K : Nat → Thread sE Bn) (s : SSig) :
    Ctx.lookup name (csl_context s) = some value →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K)) (some i) s ~
      interp_schedule_nd sh (n + 1) (ts.set i (K value)) none s := by
  grind

theorem interp_nd_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (s : SSig) :
    Ctx.lookup name (csl_context s) = none →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K)) (some i) s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  grind

/-! ## Focused source instructions under the nondeterministic runner -/

theorem interp_nd_source_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (x : A) (K : Option A → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1) (ts.set i (K (some x))) (some i) σ := by
  rw [source_raw_ret]

theorem interp_nd_source_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) σ ~
      (interp_state sh (heap_read (E := sE) (B := Bn) a) σ >>= fun p =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some p.1))) (some i) p.2) :=
  interp_schedule_nd_user_bind sh n ts i _ (.inl (.read a)) (fun x => K (some x)) σ
    (source_raw_read_head a K)

theorem interp_nd_source_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) σ ~
      (interp_state sh (heap_alloc (E := sE) (B := Bn) size) σ >>= fun p =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some p.1))) (some i) p.2) :=
  interp_schedule_nd_user_bind sh n ts i _ (.inl (.alloc size)) (fun x => K (some x)) σ
    (source_raw_alloc_head size K)

theorem interp_nd_source_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i) σ ~
      (interp_state sh (heap_cas (E := sE) (B := Bn) a expected desired) σ >>= fun p =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some p.1))) (some i) p.2) :=
  interp_schedule_nd_user_bind sh n ts i _ (.inl (.cas a expected desired))
    (fun x => K (some x)) σ (source_raw_cas_head a expected desired K)

theorem interp_nd_source_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a v : Nat) (K : Option Unit → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i) σ ~
      (interp_state sh (heap_write (E := sE) (B := Bn) a v) σ >>= fun p =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i) p.2) :=
  interp_schedule_nd_user_bind sh n ts i _ (.inl (.write a v)) (fun _ => K (some ())) σ
    (source_raw_write_head a v K)

theorem interp_nd_source_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (q v : Nat) (K : Option Unit → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.emit q v) >>= K)) (some i) σ ~
      (interp_state sh (semit q v) σ >>= fun p =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i) p.2) :=
  interp_schedule_nd_user_bind sh n ts i _ (.inr (.inr (q, v))) (fun _ => K (some ())) σ
    (source_raw_emit_head q v K)

theorem interp_nd_source_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn)
    (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow p >>= fun r =>
          match r with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) σ := by
  exact congrArg (fun t => interp_schedule_nd sh (n + 1) (ts.set i t) (some i) σ)
    ((source_raw_bind p next K).trans (congrArg _ (funext fun r => by cases r <;> rfl)))

theorem interp_nd_source_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow .yield >>= K)) (some i) σ ~
      interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) none σ := by
  grind

theorem interp_nd_source_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg Unit) (K : Option Unit → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.fork p) >>= K)) (some i) σ ~
      interp_schedule_nd sh (n + 2)
        (Vector.cons (denote_flow p >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) σ := by
  grind

theorem interp_nd_source_until_none {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) σ =
      interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow body >>= fun r =>
          match r with
          | none => K none
          | some none => K (some ())
          | some (some _) => .guard (denote_flow (.untilNone body) >>= K)))
        (some i) σ := by
  exact congrArg (fun t => interp_schedule_nd sh (n + 1) (ts.set i t) (some i) σ)
    ((source_raw_until body K).trans
      (congrArg _ (funext fun r => by rcases r with _ | _ | _ <;> rfl)))

/-! ## Handler-resolved equations -/

/-- The first-fit witness of a finite heap, independent of any handler. -/
theorem first_fit_exists (h : Heap) (size : Nat) :
    heap_finite h → 0 < size →
    ∃ base, 0 < base ∧ block_free h base size ∧
      ∀ j, 0 < j → j < base → ¬ block_free h j size := by
  intro hfin hpos
  obtain ⟨base, hb, hfree, hfirst, -⟩ :=
    heap_handler_alloc_finite (F := Bn) (B := Bn) (Sig := Unit) h (fun _ => none) size () hfin hpos
  exact ⟨base, hb, hfree, hfirst⟩

/-- Lift a rule stated for the first-fit base to the universally quantified one. -/
theorem first_fit_iff {h : Heap} {size : Nat} {L : Prop} {R : Nat → Prop}
    (hfin : heap_finite h) (hpos : 0 < size)
    (hfirst : ∀ base, 0 < base → block_free h base size →
      (∀ j, 0 < j → j < base → ¬ block_free h j size) → (L ↔ R base)) :
    L ↔ ∀ base, 0 < base → block_free h base size →
      (∀ j, 0 < j → j < base → ¬ block_free h j size) → R base :=
  ⟨fun hl base hb hf hfi => (hfirst base hb hf hfi).1 hl,
   fun hall => let ⟨base, hb, hf, hfi⟩ := first_fit_exists h size hfin hpos
     (hfirst base hb hf hfi).2 (hall base hb hf hfi)⟩

/-- Successful checked writes expose their post-operation memory before continuing at the same
focus. -/
theorem interp_nd_source_write_present (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a v : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a ≠ none →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (log (CSLObs.heap (upd h a v, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          ((upd h a v, allocs), (ctx, c))) := by
  grind

theorem interp_nd_source_read_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a = some value →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      interp_schedule_nd sh (n + 1) (ts.set i (K (some value))) (some i)
        ((h, allocs), (ctx, c)) := by
  grind

theorem interp_nd_source_emit_log (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K)) (some i)
        (memory, (ctx, c)) ~
      (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory, (ctx, c + 1))) := by
  grind

theorem interp_nd_source_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    h a = some current →
    interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (if current = expected then
        log (CSLObs.heap (upd h a desired, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
            ((upd h a desired, allocs), (ctx, c))
      else
        interp_schedule_nd sh (n + 1) (ts.set i (K (some false))) (some i)
          ((h, allocs), (ctx, c))) := by
  grind

theorem interp_nd_source_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
          (managed_alloc (h, allocs) base size, (ctx, c))) := by
  intro hpos hbase hfree hfirst
  grind [sh_alloc_first h allocs size base (ctx, c) hpos hbase hfree hfirst]

theorem interp_nd_source_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a = none →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  grind

theorem interp_nd_source_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a v : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h a = none →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.write a v) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  grind

theorem interp_nd_source_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    h a = none →
    interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  grind

/-! Whole-block free preserves focus. Nonzero success logs the released memory; free zero is
silent, and invalid free is a fault. -/

theorem source_free_raw_heap_free (base : Nat) (K : Option Unit → Thread sE Bn) :
    (denote_flow (.free base) >>= K) = (heap_free (E := CEff) (B := Bn) base >>= fun _ =>
      K (some ())) :=
  (source_raw_free_head base K).trans (raw_heap_free_head base _).symm

theorem interp_nd_source_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (memory memory' : ManagedHeap) (ctx : Ctx) (c : Nat) :
    managed_free memory base = some memory' →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.free base) >>= K)) (some i)
        (memory, (ctx, c)) ~
      match base with
      | 0 => interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i) (memory', (ctx, c))
      | _ + 1 => log (CSLObs.heap memory' : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            (memory', (ctx, c)) := by
  intro hfree
  rw [source_free_raw_heap_free]
  exact interp_nd_heap_free n ts i base (fun _ => K (some ())) memory memory' ctx c hfree

theorem interp_nd_source_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    managed_free memory base = none →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.free base) >>= K)) (some i)
        (memory, (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  intro hinv
  rw [source_free_raw_heap_free]
  exact interp_nd_heap_free_invalid n ts i base (fun _ => K (some ())) memory ctx c hinv

/-! ## Source-instruction first-yield rules, in exact mode -/

theorem exact_source_bind {A B : Type} (p : CProg A) (next : A → CProg B)
    (K : Option B → Thread sE Bn) (σ : SSig) (logs : List (CSLObs (Nat × Nat)))
    (target : Thread sE Bn) (σ' : SSig) :
    segment_to sh csl_equ (denote_flow p >>= fun flow =>
        match flow with
        | none => K none
        | some x => denote_flow (next x) >>= K) σ logs target σ' →
    segment_to sh csl_equ (denote_flow (.bind p next) >>= K) σ logs target σ' :=
  segment_to_equ sh csl_equ _ _ σ logs target σ'
    ((source_raw_bind p next K).trans (congrArg _ (funext fun r => by cases r <;> rfl)))

theorem exact_source_ret {A : Type} (x : A) (K : Option A → Thread sE Bn) (σ : SSig)
    (logs : List (CSLObs (Nat × Nat))) (target : Thread sE Bn) (σ' : SSig) :
    segment_to sh csl_equ (K (some x)) σ logs target σ' →
    segment_to sh csl_equ (denote_flow (.ret x) >>= K) σ logs target σ' :=
  segment_to_equ sh csl_equ _ _ σ logs target σ' (source_raw_ret x K)

theorem exact_source_until {A : Type} (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (σ : SSig) (logs : List (CSLObs (Nat × Nat))) (target : Thread sE Bn) (σ' : SSig) :
    segment_to sh csl_equ (denote_flow body >>= until_tail body K) σ logs target σ' →
    segment_to sh csl_equ (denote_flow (.untilNone body) >>= K) σ logs target σ' :=
  segment_to_equ sh csl_equ _ _ σ logs target σ' (source_raw_until body K)

theorem exact_source_read (a v : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (logs : List (CSLObs (Nat × Nat))) (target : Thread sE Bn)
    (σ' : SSig) :
    h a = some v →
    segment_to sh csl_equ (K (some v)) ((h, allocs), (ctx, c)) logs target σ' →
    segment_to sh csl_equ (denote_flow (.read a) >>= K) ((h, allocs), (ctx, c)) logs target σ' := by
  rintro hr ⟨residual, hseg, htail⟩
  refine ⟨residual, ?_, htail⟩
  rw [source_raw_read_head]
  refine .user _ _ _ _ _ [] logs residual σ' ?_ hseg
  exact heap_handlerW_rd_some CSLObs.heap a h allocs (ctx, c) v hr

theorem exact_source_write (a v : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (logs : List (CSLObs (Nat × Nat))) (target : Thread sE Bn)
    (σ' : SSig) :
    h a ≠ none →
    segment_to sh csl_equ (K (some ())) ((upd h a v, allocs), (ctx, c)) logs target σ' →
    segment_to sh csl_equ (denote_flow (.write a v) >>= K) ((h, allocs), (ctx, c))
      (CSLObs.heap (upd h a v, allocs) :: logs) target σ' := by
  rintro hp ⟨residual, hseg, htail⟩
  cases hw : h a with
  | none => exact absurd hw hp
  | some w =>
    refine ⟨residual, ?_, htail⟩
    rw [source_raw_write_head]
    refine .user _ _ _ ?r _ [CSLObs.heap (upd h a v, allocs)] logs residual σ' ?p hseg
    case p => exact heap_handlerW_wr_some CSLObs.heap a h allocs (ctx, c) v w hw

/-- The raw handler equation `csl_emit_handler_log` is the response certificate here. -/
theorem exact_source_emit (tag block : Nat) (K : Option Unit → Thread sE Bn)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (logs : List (CSLObs (Nat × Nat)))
    (target : Thread sE Bn) (σ' : SSig) :
    segment_to sh csl_equ (K (some ())) (memory, (ctx, c + 1)) logs target σ' →
    segment_to sh csl_equ (denote_flow (.emit tag block) >>= K) (memory, (ctx, c))
      (CSLObs.emit (stamp (tag, block) c) :: logs) target σ' := by
  rintro ⟨residual, hseg, htail⟩
  refine ⟨residual, ?_, htail⟩
  rw [source_raw_emit_head]
  refine .user _ _ _ ?r _ [CSLObs.emit (stamp (tag, block) c)] logs residual σ' ?p hseg
  case p => exact csl_emit_handler_log (tag, block) memory ctx c

theorem exact_source_cas_success (a expected desired : Nat) (K : Option Bool → Thread sE Bn)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (logs : List (CSLObs (Nat × Nat)))
    (target : Thread sE Bn) (σ' : SSig) :
    h a = some expected →
    segment_to sh csl_equ (K (some true)) ((upd h a desired, allocs), (ctx, c)) logs target σ' →
    segment_to sh csl_equ (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)
      ((h, allocs), (ctx, c)) (CSLObs.heap (upd h a desired, allocs) :: logs) target σ' := by
  rintro hr ⟨residual, hseg, htail⟩
  refine ⟨residual, ?_, htail⟩
  rw [source_raw_cas_head]
  refine .user _ _ _ _ _ [CSLObs.heap (upd h a desired, allocs)] logs residual σ' ?_ hseg
  exact heap_handlerW_cas_success CSLObs.heap a expected desired h allocs (ctx, c) hr

theorem exact_source_cas_failure (a expected desired current : Nat)
    (K : Option Bool → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (logs : List (CSLObs (Nat × Nat))) (target : Thread sE Bn) (σ' : SSig) :
    h a = some current → current ≠ expected →
    segment_to sh csl_equ (K (some false)) ((h, allocs), (ctx, c)) logs target σ' →
    segment_to sh csl_equ (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)
      ((h, allocs), (ctx, c)) logs target σ' := by
  rintro hr hne ⟨residual, hseg, htail⟩
  refine ⟨residual, ?_, htail⟩
  rw [source_raw_cas_head]
  refine .user _ _ _ _ _ [] logs residual σ' ?_ hseg
  exact heap_handlerW_cas_failure CSLObs.heap a expected desired current h allocs (ctx, c) hr hne

theorem exact_source_free (base : Nat) (K : Option Unit → Thread sE Bn)
    (memory memory' : ManagedHeap) (ctx : Ctx) (c : Nat) (logs : List (CSLObs (Nat × Nat)))
    (target : Thread sE Bn) (σ' : SSig) :
    managed_free memory base = some memory' →
    segment_to sh csl_equ (K (some ())) (memory', (ctx, c)) logs target σ' →
    segment_to sh csl_equ (denote_flow (.free base) >>= K) (memory, (ctx, c))
      ((match base with | 0 => [] | _ + 1 => [CSLObs.heap memory']) ++ logs) target σ' := by
  rintro hfree ⟨residual, hseg, htail⟩
  refine ⟨residual, ?_, htail⟩
  rw [source_raw_free_head]
  have hh := heap_handlerW_free (B := Bn) (CSLObs.heap (A := Nat × Nat)) base memory memory'
    (ctx, c) hfree
  cases base with
  | zero =>
    refine .user _ _ _ ?r _ [] logs residual σ' ?p hseg
    case p => exact hh
  | succ b =>
    refine .user _ _ _ ?r _ [CSLObs.heap memory'] logs residual σ' ?p hseg
    case p => exact hh

theorem exact_source_yield (K : Option Unit → Thread sE Bn) (σ : SSig) (target : Thread sE Bn) :
    guard_equ (K (some ())) target →
    segment_to sh csl_equ (denote_flow .yield >>= K) σ [] target σ := by
  intro htail
  refine ⟨K (some ()), ?_, htail⟩
  rw [source_raw_yield_head]
  exact .yield _ σ

-- Not ported (outside this file's scope or not declarations):
-- `interp_rr_*`, `interp_fair_*`, `run_rr_fork_bind`, `run_fair_fork_bind` (policy family, in
-- `Lang/CoCSL/RunnersFair.lean`); Ltacs `csl_monad_bind` (Lean `>>=` is already `CTree.bind`)
-- and `csl_raw_equ` (use `simp only [source_raw_bind, source_raw_ret, bind_assoc, pure_bind']`
-- or `rw` with these equations).

end CoCSL
