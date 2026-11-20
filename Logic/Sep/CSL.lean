/- SPDX-License-Identifier: MIT -/
module

public import Logic.Interp.Heap
public import Logic.CTree.Heap
public import Logic.CTree.TraceRules
public import Logic.CTree.AF
public import Logic.CTree.EF
public import Logic.CTree.AG
public import Logic.CTree.EG
public import Logic.Yield.Nondeterministic
public import Logic.Yield.RoundRobin
public import Logic.Utils.Maps

/-!
# The canonical CSL effect interpreter

The CSL effect sum, its interpretation state, and the payload-polymorphic handler `sh` combining
the shared checked heap, the shared variable context (with context-update observations) and the
shared indexing writer. Stated over effects and trees only; the whole stack is fixed at the
finite branch signature `Bn` (← `CTree/Interp/CSL/Mod.v`).
-/

@[expose] public section
namespace Tisl.CSL
open CTree Coinduction Notation Tisl.Heap Tisl.Ctx Tisl.Yield
open ITree (Effect)

/-! ## Effects and interpretation state -/

/-- The CSL user effects at the tagged payload `Nat × Nat`. -/
abbrev sE : Effect.{0} := heapE ⊕ₑ stateE Ctx ⊕ₑ writerE (Nat × Nat)

/-- Interpretation state `((h, allocs), (ctx, c))`: shared managed memory, shared variable
context, and one global occurrence counter for indexed emissions. -/
abbrev SSig : Type := ManagedHeap × (Ctx × Nat)

/-- Mutation snapshots, context updates and indexed user emissions. -/
inductive CSLObs (A : Type) : Type
  | heap (memory : ManagedHeap)
  | ctx (context : Ctx)
  | emit (emission : Indexed A)

def csl_heap {A : Type} (P : ManagedHeap → Prop) : CSLObs A → Prop
  | .heap memory => P memory
  | _ => False

/-- Thread effects: yield, fork and the interpreted sum. -/
abbrev CEff : Effect.{0} := yieldE ⊕ₑ forkE ⊕ₑ sE

def csl_memory (s : SSig) : ManagedHeap := s.1
def csl_context (s : SSig) : Ctx := s.2.1
def csl_counter (s : SSig) : Nat := s.2.2
def csl_set_context (s : SSig) (ctx : Ctx) : SSig := (csl_memory s, (ctx, csl_counter s))

def csl_indexed {A : Type} (P : Indexed A → Prop) : CSLObs A → Prop
  | .emit x => P x
  | _ => False

/-- Heap and context observations carry no occurrence index and project to `0`. -/
def csl_index {A : Type} : CSLObs A → Nat
  | .emit x => x.index
  | _ => 0

/-- Payload-only matching on actual labels; stamps remain internal data. -/
def csl_label_emits {A : Type} (P : A → Prop) : Label (writerE (CSLObs A)) → Prop :=
  log_label (csl_indexed fun emission => P emission.value)

theorem csl_label_emits_emit {A : Type} (P : A → Prop) (a : A) (j : Nat) :
    csl_label_emits P (.obs (E := writerE (CSLObs A)) (.emit (stamp a j)) ⟨⟩) ↔ P a := Iff.rfl

/-- Fresh emissions above every bound force a recurrently taken emission label. -/
theorem csl_fresh_implies_recurrent_emission {A X : Type} {B : Effect.{0}} (P : A → Prop)
    (P_dec : ∀ a, Decidable (P a)) (t : ctreeW (CSLObs A) B X)
    (w : World (writerE (CSLObs A))) :
    (∀ k, entails (AG (AF (visWₜ (csl_indexed (indexed_after P k))))) t w) →
    RecurrentLabel (csl_label_emits P) t := by
  refine agaf_family_recurrent_label _ (fun k => csl_indexed (indexed_after P k)) ?_ ?_ ?_ t w
  · rintro (_ | _ | e)
    · exact instDecidableFalse
    · exact instDecidableFalse
    · exact P_dec e.value
  · rintro k (_ | _ | e) h
    · exact h
    · exact h
    · exact h.1
  · rintro (_ | _ | e)
    · exact ⟨0, id⟩
    · exact ⟨0, id⟩
    · exact ⟨e.index + 1, fun h => Nat.not_succ_le_self _ h.2⟩

/-- Payload matching on instrumented runs ignores scheduling labels. -/
def csl_label_emitsW {A : Type} (P : A → Prop) : Label (writerE (CSLObs A ⊕ Nat)) → Prop :=
  log_label (fair_obs (csl_indexed fun emission => P emission.value))

theorem csl_label_emitsW_emit {A : Type} (P : A → Prop) (a : A) (j : Nat) :
    csl_label_emitsW P (.obs (E := writerE (CSLObs A ⊕ Nat)) (.inl (.emit (stamp a j))) ⟨⟩) ↔
      P a := Iff.rfl

/-- `csl_fresh_implies_recurrent_emission` on instrumented runs. -/
theorem csl_fresh_implies_recurrent_emissionW {A X : Type} {B : Effect.{0}} (P : A → Prop)
    (P_dec : ∀ a, Decidable (P a)) (t : ctreeW (CSLObs A ⊕ Nat) B X)
    (w : World (writerE (CSLObs A ⊕ Nat))) :
    (∀ k, entails (AG (AF (visWₜ (fair_obs (csl_indexed (indexed_after P k)))))) t w) →
    RecurrentLabel (csl_label_emitsW P) t := by
  refine agaf_family_recurrent_label _ (fun k => fair_obs (csl_indexed (indexed_after P k)))
    ?_ ?_ ?_ t w
  · rintro ((_ | _ | e) | _)
    · exact instDecidableFalse
    · exact instDecidableFalse
    · exact P_dec e.value
    · exact instDecidableFalse
  · rintro k ((_ | _ | e) | _) h
    · exact h
    · exact h
    · exact h.1
    · exact h
  · rintro ((_ | _ | e) | _)
    · exact ⟨0, id⟩
    · exact ⟨0, id⟩
    · exact ⟨e.index + 1, fun h => Nat.not_succ_le_self _ h.2⟩
    · exact ⟨0, id⟩

/-- Only user emissions, in order. -/
def csl_emissions {A : Type} : List (CSLObs A) → List (Indexed A)
  | [] => []
  | .emit emission :: rest => emission :: csl_emissions rest
  | _ :: rest => csl_emissions rest

theorem csl_emissions_in {A : Type} (emission : Indexed A) (logs : List (CSLObs A)) :
    emission ∈ csl_emissions logs ↔ CSLObs.emit emission ∈ logs := by
  induction logs with
  | nil => simp [csl_emissions]
  | cons o rest ih => cases o <;> simp [csl_emissions, ih, eq_comm]

theorem csl_emissions_heap_prefix {A : Type} (heaps : List ManagedHeap) (logs : List (CSLObs A)) :
    csl_emissions (heaps.map CSLObs.heap ++ logs) = csl_emissions logs := by
  induction heaps with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem csl_emissions_heaps {A : Type} (heaps : List ManagedHeap) :
    csl_emissions (A := A) (heaps.map CSLObs.heap) = [] := by
  induction heaps with
  | nil => rfl
  | cons _ _ ih => exact ih

def semit (q v : Nat) : CTree sE Bn PUnit :=
  CTree.trigger (E := sE) (.inr (.inr (q, v)))

/-- `get` is silent; `put` logs the new context; memory and counter are untouched. -/
def csl_context_handler {A : Type} :
    (e : (stateE Ctx).I) → StateT SSig (ctreeW (CSLObs A) Bn) ((stateE Ctx).O e)
  | .get => fun s => pure (csl_context s, s)
  | .put ctx' => fun s =>
    log (CSLObs.ctx ctx' : CSLObs A) >>= fun _ => pure (⟨⟩, csl_set_context s ctx')

/-- Every log emits exactly one `emit` stamp and advances only the counter. -/
def csl_emit_handler {A : Type} :
    (e : (writerE A).I) → StateT SSig (ctreeW (CSLObs A) Bn) ((writerE A).O e) :=
  fun a s =>
    log (CSLObs.emit (stamp a (csl_counter s))) >>= fun _ =>
      pure (⟨⟩, (csl_memory s, (csl_context s, csl_counter s + 1)))

/-- The one CSL handler, polymorphic in the observation payload. -/
def sh {A : Type} : (e : (heapE ⊕ₑ stateE Ctx ⊕ₑ writerE A).I) →
    StateT SSig (ctreeW (CSLObs A) Bn) ((heapE ⊕ₑ stateE Ctx ⊕ₑ writerE A).O e) :=
  h_sum (heap_handlerW CSLObs.heap) (h_sum csl_context_handler csl_emit_handler)

/-! ### Raw handler equations -/

@[simp] theorem csl_context_handler_get {A : Type} (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    csl_context_handler (A := A) StateOp.get (memory, (ctx, c)) =
      (pure (ctx, (memory, (ctx, c))) : ctreeW (CSLObs A) Bn (Ctx × SSig)) := rfl

@[simp] theorem csl_context_handler_put {A : Type} (ctx' : Ctx) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) :
    csl_context_handler (A := A) (StateOp.put ctx') (memory, (ctx, c)) =
      (log (CSLObs.ctx ctx' : CSLObs A) >>= fun _ => pure (⟨⟩, (memory, (ctx', c)))) := rfl

@[simp] theorem csl_emit_handler_log {A : Type} (a : A) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) :
    csl_emit_handler (A := A) a (memory, (ctx, c)) =
      (log (CSLObs.emit (stamp a c)) >>= fun _ => pure (⟨⟩, (memory, (ctx, c + 1)))) := rfl

/-! ### `sh` equations for `grind`

Logged responses are stated with `Functor.mapConst` (see `Tisl.mapConst_bind`), and `@Eq _` types
the right-hand side at the handler's own response type `(sE.O e) × SSig`, so that `grind`'s
congruence closure meets one type on both sides. -/

section ShGrind
variable {A : Type}

@[grind =] theorem sh_get (s : SSig) :
    @Eq _ (sh (A := A) (.inr (.inl .get)) s) (pure (csl_context s, s)) := rfl

@[grind =] theorem sh_put (ctx' : Ctx) (s : SSig) :
    @Eq _ (sh (A := A) (.inr (.inl (.put ctx'))) s)
      (Functor.mapConst (⟨⟩, csl_set_context s ctx') (log (CSLObs.ctx ctx'))) := rfl

@[grind =] theorem sh_emit (a : A) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    @Eq _ (sh (.inr (.inr a)) (memory, (ctx, c)))
      (Functor.mapConst (⟨⟩, (memory, (ctx, c + 1))) (log (CSLObs.emit (stamp a c)))) := rfl

@[grind =] theorem sh_read (a : Nat) (h allocs : Heap) (aux : Ctx × Nat) :
    @Eq _ (sh (A := A) (.inl (.read a)) ((h, allocs), aux))
      (match h a with
       | some v => pure (v, ((h, allocs), aux))
       | none => .stuck) := by
  cases hv : h a with
  | some v => exact heap_handlerW_rd_some CSLObs.heap a h allocs aux v hv
  | none => exact heap_handlerW_rd_none CSLObs.heap a h allocs aux hv

@[grind =] theorem sh_write (a v : Nat) (h allocs : Heap) (aux : Ctx × Nat) :
    @Eq _ (sh (A := A) (.inl (.write a v)) ((h, allocs), aux))
      (match h a with
       | some _ =>
         Functor.mapConst (⟨⟩, ((upd h a v, allocs), aux)) (log (CSLObs.heap (upd h a v, allocs)))
       | none => .stuck) := by
  cases hv : h a with
  | some w => exact heap_handlerW_wr_some CSLObs.heap a h allocs aux v w hv
  | none => exact heap_handlerW_wr_none CSLObs.heap a h allocs aux v hv

@[grind =] theorem sh_cas (a expected desired : Nat) (h allocs : Heap) (aux : Ctx × Nat) :
    @Eq _ (sh (A := A) (.inl (.cas a expected desired)) ((h, allocs), aux))
      (match h a with
       | some current =>
         if current = expected then
           Functor.mapConst (true, ((upd h a desired, allocs), aux))
             (log (CSLObs.heap (upd h a desired, allocs)))
         else pure (false, ((h, allocs), aux))
       | none => .stuck) := by
  cases hv : h a with
  | some current =>
    by_cases hc : current = expected
    · subst hc; simp only [↓reduceIte]
      exact heap_handlerW_cas_success CSLObs.heap a current desired h allocs aux hv
    · simp only [hc, ↓reduceIte]
      exact heap_handlerW_cas_failure CSLObs.heap a expected desired current h allocs aux hv hc
  | none => exact heap_handlerW_cas_missing CSLObs.heap a expected desired h allocs aux hv

@[grind =] theorem sh_free (base : Nat) (memory : ManagedHeap) (aux : Ctx × Nat) :
    @Eq _ (sh (A := A) (.inl (.free base)) (memory, aux))
      (match managed_free memory base with
       | some memory' =>
         match base with
         | 0 => pure (⟨⟩, (memory', aux))
         | _ + 1 => Functor.mapConst (⟨⟩, (memory', aux)) (log (CSLObs.heap memory'))
       | none => .stuck) := by
  cases hf : managed_free memory base with
  | some m' => exact heap_handlerW_free CSLObs.heap base memory m' aux hf
  | none => exact heap_handlerW_free_invalid CSLObs.heap base memory aux hf

/-- First-fit allocation; not a `grind` rule (its side conditions do not determine `base`), so
pass an instance to `grind [sh_alloc_first ...]`. -/
theorem sh_alloc_first (h allocs : Heap) (size base : Nat) (aux : Ctx × Nat) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    @Eq _ (sh (A := A) (.inl (.alloc size)) ((h, allocs), aux))
      (guards (base - 1) (Functor.mapConst (base, (managed_alloc (h, allocs) base size, aux))
        (log (CSLObs.heap (managed_alloc (h, allocs) base size))))) :=
  heap_handlerW_alloc_first_guards CSLObs.heap h allocs size base aux

end ShGrind

/-- Interpretation-level emission: exactly one `emit` stamp. -/
theorem interp_csl_emit {A X : Type} (a : A) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (k : PUnit → CTree (heapE ⊕ₑ stateE Ctx ⊕ₑ writerE A) Bn X) :
    interp_state sh
      (CTree.trigger (E := heapE ⊕ₑ stateE Ctx ⊕ₑ writerE A) (.inr (.inr a)) >>= k)
      (memory, (ctx, c)) ~
    (log (CSLObs.emit (stamp a c)) >>= fun _ => interp_state sh (k ⟨⟩) (memory, (ctx, c + 1))) := by
  grind [interp_state_bind]

/-! ## Thread effects -/

def source_yield : CTree CEff Bn PUnit := .vis (.inl ⟨⟩) fun _ => pure ⟨⟩
def source_fork : CTree CEff Bn Bool := .vis (.inr (.inl ⟨⟩)) fun b => pure b
def source_get : CTree CEff Bn Ctx := CTree.trigger (E := CEff) (.inr (.inr (.inr (.inl .get))))
def source_put (ctx : Ctx) : CTree CEff Bn PUnit :=
  CTree.trigger (E := CEff) (.inr (.inr (.inr (.inl (.put ctx)))))

/-! ## The two response-relation instances of the generic segment theory -/

abbrev csl_sb : (X : Type) → ctreeW (CSLObs (Nat × Nat)) Bn X →
    ctreeW (CSLObs (Nat × Nat)) Bn X → Prop := fun _ t u => t ~ u
abbrev csl_equ : (X : Type) → ctreeW (CSLObs (Nat × Nat)) Bn X →
    ctreeW (CSLObs (Nat × Nat)) Bn X → Prop := fun _ t u => t = u

/-! ## Raw physical free through the shared heap event -/

@[grind =] theorem raw_heap_free_head (a : Nat) (K : PUnit → Thread sE Bn) :
    (heap_free (E := CEff) a >>= K) = .vis (E := CEff) (.inr (.inr (.inl (.free a)))) K := by
  rw [heap_free, bind_trigger']; rfl

theorem interp_rr_heap_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : PUnit → Thread sE Bn) (m : Nat) (memory memory' : ManagedHeap) (ctx : Ctx) (c : Nat) :
    managed_free memory base = some memory' →
    interp_schedule_rr sh (n + 1) (ts.set i (heap_free base >>= K)) (some i) m
      (memory, (ctx, c)) ~
    match base with
    | 0 => interp_schedule_rr sh (n + 1) (ts.set i (K ⟨⟩)) (some i) m (memory', (ctx, c))
    | _ + 1 => log (.inl (CSLObs.heap memory')) >>= fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K ⟨⟩)) (some i) m (memory', (ctx, c)) := by
  intro hfree
  cases base <;> grind

theorem interp_rr_heap_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : PUnit → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) :
    managed_free memory base = none →
    interp_schedule_rr sh (n + 1) (ts.set i (heap_free base >>= K)) (some i) m
      (memory, (ctx, c)) ~
    (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  grind

theorem interp_nd_heap_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : PUnit → Thread sE Bn) (memory memory' : ManagedHeap) (ctx : Ctx) (c : Nat) :
    managed_free memory base = some memory' →
    interp_schedule_nd sh (n + 1) (ts.set i (heap_free base >>= K)) (some i)
      (memory, (ctx, c)) ~
    match base with
    | 0 => interp_schedule_nd sh (n + 1) (ts.set i (K ⟨⟩)) (some i) (memory', (ctx, c))
    | _ + 1 => log (CSLObs.heap memory') >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K ⟨⟩)) (some i) (memory', (ctx, c)) := by
  intro hfree
  cases base <;> grind

theorem interp_nd_heap_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : PUnit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    managed_free memory base = none →
    interp_schedule_nd sh (n + 1) (ts.set i (heap_free base >>= K)) (some i)
      (memory, (ctx, c)) ~
    (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  grind

/-! ## Shared-context access through the scheduler

`get` substitutes the current context silently; `put` emits exactly the new context. Neither
changes focus or the RR cursor, nor touches memory or the indexed counter. -/

@[grind =] theorem raw_source_get_head {X : Type} (K : Ctx → CTree CEff Bn X) :
    (source_get >>= K) = .vis (E := CEff) (.inr (.inr (.inr (.inl .get)))) K :=
  bind_trigger _ _

@[grind =] theorem raw_source_put_head {X : Type} (ctx' : Ctx) (K : PUnit → CTree CEff Bn X) :
    (source_put ctx' >>= K) = .vis (E := CEff) (.inr (.inr (.inr (.inl (.put ctx'))))) K :=
  bind_trigger _ _

theorem interp_nd_get_ctx (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Ctx → Thread sE Bn) (s : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (source_get >>= K)) (some i) s ~
      interp_schedule_nd sh (n + 1) (ts.set i (K (csl_context s))) (some i) s := by
  grind

theorem interp_rr_get_ctx (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Ctx → Thread sE Bn) (cursor : Nat) (s : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (source_get >>= K)) (some i) cursor s ~
      interp_schedule_rr sh (n + 1) (ts.set i (K (csl_context s))) (some i) cursor s := by
  grind

theorem interp_nd_put_ctx (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ctx' : Ctx)
    (K : PUnit → Thread sE Bn) (s : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (source_put ctx' >>= K)) (some i) s ~
      (log (CSLObs.ctx ctx' : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_schedule_nd sh (n + 1) (ts.set i (K ⟨⟩)) (some i) (csl_set_context s ctx')) := by
  grind

theorem interp_rr_put_ctx (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ctx' : Ctx)
    (K : PUnit → Thread sE Bn) (cursor : Nat) (s : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (source_put ctx' >>= K)) (some i) cursor s ~
      (log (.inl (CSLObs.ctx ctx') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        interp_schedule_rr sh (n + 1) (ts.set i (K ⟨⟩)) (some i) cursor
          (csl_set_context s ctx')) := by
  grind

/-! ## Standalone erased threads over the CSL handler

`Fork` resolves to the parent branch and `Yield` is erased; context access behaves exactly as
under the schedulers. -/

theorem interp_thread_get_ctx {X : Type} (K : Ctx → CTree CEff Bn X) (s : SSig) :
    interp_state sh (interp_thread (source_get >>= K)) s ~
      interp_state sh (interp_thread (K (csl_context s))) s := by
  grind

theorem interp_thread_put_ctx {X : Type} (ctx' : Ctx) (K : PUnit → CTree CEff Bn X) (s : SSig) :
    interp_state sh (interp_thread (source_put ctx' >>= K)) s ~
      (log (CSLObs.ctx ctx' : CSLObs (Nat × Nat)) >>= fun _ =>
        interp_state sh (interp_thread (K ⟨⟩)) (csl_set_context s ctx')) := by
  grind

/-- A read-modify-write of the shared context leaves exactly one context observation. -/
theorem interp_thread_ctx_update {X : Type} (f : Ctx → Ctx) (r : X) (s : SSig) :
    interp_state sh (interp_thread
      (source_get >>= fun ctx => source_put (f ctx) >>= fun _ => pure r)) s ~
    (log (CSLObs.ctx (f (csl_context s)) : CSLObs (Nat × Nat)) >>= fun _ =>
      pure (r, csl_set_context s (f (csl_context s))) :
      ctreeW (CSLObs (Nat × Nat)) Bn (X × SSig)) := by
  refine sbisim_trans (interp_thread_get_ctx _ s) ?_
  refine sbisim_trans (interp_thread_put_ctx _ _ s) ?_
  simp only [interp_state_thread_ret]
  exact sbisim_refl _

/-! ## Selection from an unfocused nonempty pool

The non-deterministic scheduler picks with one visible branch (`brSn`); round robin picks with
one logged scheduling slot. -/

section Select
variable (n : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) {i : Option Type}

section ND
variable (ts : Pool sE Bn (n + 1)) (w : World (writerE (CSLObs (Nat × Nat))))
  (φ : TiclL (writerE (CSLObs (Nat × Nat)))) (ψ : Ticl (writerE (CSLObs (Nat × Nat))) i)

theorem an_csl_nd_select :
    entails (φ AN ψ) (interp_schedule_nd sh (n + 1) ts none (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∧
      ∀ j : Fin (n + 1),
        entails ψ (interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_schedule_nd_select sh n ts _)]
  exact (an_brS (B := Bn) (c := ⟨n + 1⟩) ⟨0⟩).trans
    (and_congr_right' ⟨fun h j => h ⟨j⟩, fun h j => h j.down⟩)

theorem au_csl_nd_select :
    entails (φ AU ψ) (interp_schedule_nd sh (n + 1) ts none (memory, (ctx, c))) w ↔
      entails ψ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∨
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∧
      ∀ j : Fin (n + 1),
        entails (φ AU ψ) (interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_schedule_nd_select sh n ts _)]
  exact (au_brS (B := Bn) (c := ⟨n + 1⟩) ⟨0⟩).symm.trans
    (or_congr_right (and_congr_right' ⟨fun h j => h ⟨j⟩, fun h j => h j.down⟩))

theorem ag_csl_nd_select :
    entails (AG φ) (interp_schedule_nd sh (n + 1) ts none (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∧
      ∀ j : Fin (n + 1),
        entails (AG φ) (interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_schedule_nd_select sh n ts _)]
  exact (ag_brS (B := Bn) (c := ⟨n + 1⟩) ⟨0⟩).symm.trans
    (and_congr_right' ⟨fun h j => h ⟨j⟩, fun h j => h j.down⟩)

theorem en_csl_nd_select :
    entails (φ EN ψ) (interp_schedule_nd sh (n + 1) ts none (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∧
      ∃ j : Fin (n + 1),
        entails ψ (interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_schedule_nd_select sh n ts _)]
  exact (en_brS (B := Bn) (c := ⟨n + 1⟩)).trans
    (and_congr_right' ⟨fun ⟨j, h⟩ => ⟨j.down, h⟩, fun ⟨j, h⟩ => ⟨⟨j⟩, h⟩⟩)

theorem eu_csl_nd_select :
    entails (φ EU ψ) (interp_schedule_nd sh (n + 1) ts none (memory, (ctx, c))) w ↔
      entails ψ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∨
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∧
      ∃ j : Fin (n + 1),
        entails (φ EU ψ) (interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_schedule_nd_select sh n ts _)]
  exact (eu_brS (B := Bn) (c := ⟨n + 1⟩)).symm.trans
    (or_congr_right (and_congr_right' ⟨fun ⟨j, h⟩ => ⟨j.down, h⟩, fun ⟨j, h⟩ => ⟨⟨j⟩, h⟩⟩))

theorem eg_csl_nd_select :
    entails (EG φ) (interp_schedule_nd sh (n + 1) ts none (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w ∧
      ∃ j : Fin (n + 1),
        entails (EG φ) (interp_schedule_nd sh (n + 1) ts (some j) (memory, (ctx, c))) w := by
  rw [proper_entails_meq _ (interp_schedule_nd_select sh n ts _)]
  exact (eg_brS (B := Bn) (c := ⟨n + 1⟩)).symm.trans
    (and_congr_right' ⟨fun ⟨j, h⟩ => ⟨j.down, h⟩, fun ⟨j, h⟩ => ⟨⟨j⟩, h⟩⟩)

end ND

section RR
local notation "WR" => writerE (CSLObs (Nat × Nat) ⊕ Nat)
variable (ts : Pool sE Bn (n + 1)) (m : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR i)

theorem an_csl_rr_select :
    entails (φ AN ψ) (interp_schedule_rr sh (n + 1) ts none m (memory, (ctx, c))) w ↔
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧
      entails ψ (interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_schedule_rr_select sh n ts m _)]
  exact (an_vis (E := WR) (B := Bn) ⟨⟩).trans (and_congr_right' ⟨fun h => h ⟨⟩, fun h _ => h⟩)

theorem au_csl_rr_select :
    entails (φ AU ψ) (interp_schedule_rr sh (n + 1) ts none m (memory, (ctx, c))) w ↔
      entails ψ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∨
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧
      entails (φ AU ψ)
        (interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_schedule_rr_select sh n ts m _)]
  exact (au_vis (E := WR) (B := Bn) ⟨⟩).symm.trans
    (or_congr_right (and_congr_right' ⟨fun h => h ⟨⟩, fun h _ => h⟩))

theorem ag_csl_rr_select :
    entails (AG φ) (interp_schedule_rr sh (n + 1) ts none m (memory, (ctx, c))) w ↔
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧
      entails (AG φ)
        (interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_schedule_rr_select sh n ts m _)]
  exact (ag_vis (E := WR) (B := Bn) ⟨⟩).symm.trans
    (and_congr_right' ⟨fun h => h ⟨⟩, fun h _ => h⟩)

theorem en_csl_rr_select :
    entails (φ EN ψ) (interp_schedule_rr sh (n + 1) ts none m (memory, (ctx, c))) w ↔
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧
      entails ψ (interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_schedule_rr_select sh n ts m _)]
  exact (en_vis (E := WR) (B := Bn)).trans
    (and_congr_right' ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩)

theorem eu_csl_rr_select :
    entails (φ EU ψ) (interp_schedule_rr sh (n + 1) ts none m (memory, (ctx, c))) w ↔
      entails ψ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∨
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧
      entails (φ EU ψ)
        (interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_schedule_rr_select sh n ts m _)]
  exact (eu_vis (E := WR) (B := Bn)).symm.trans
    (or_congr_right (and_congr_right' ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩))

theorem eg_csl_rr_select :
    entails (EG φ) (interp_schedule_rr sh (n + 1) ts none m (memory, (ctx, c))) w ↔
      entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧
      entails (EG φ)
        (interp_schedule_rr sh (n + 1) ts (some (rr_pick n m)) (m + 1) (memory, (ctx, c)))
        (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩) := by
  rw [proper_entails_meq _ (interp_schedule_rr_select sh n ts m _)]
  exact (eg_vis (E := WR) (B := Bn)).symm.trans
    (and_congr_right' ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩)

end RR
end Select

-- Not ported: `csl_lift_handler_result` (Ltac: plain `rw`).

end Tisl.CSL
