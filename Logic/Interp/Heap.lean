/- SPDX-License-Identifier: MIT -/
module

public import Logic.Interp.State
public import Logic.Events.Heap
public import Logic.Events.Writer
public import Logic.Sep.HeapModel
public import Logic.CTree.Core

/-!
# Checked heap accesses, malloc and whole-block free

One handler for `heapE`, polymorphic in its output effect `F`, branch signature `B` and an
untouched auxiliary state; the managed memory (`ManagedHeap`) is the first state component.
Allocation rejects size 0 and searches from address 1 for the first free block with silent guards;
missing reads/writes/CAS are stuck, a failed CAS leaves the state unchanged, and free is exactly
`managed_free` (← `CTree/Interp/Heap.v`). Lean's `StateT` returns `(value, state)`.
-/

@[expose] public section
namespace Tisl
open CTree Coinduction Tisl.Heap Tisl.Pcm
open ITree (Effect)

/-- Extensional equality of managed heaps from pointwise equivalence. -/
theorem managed_heap_ext (m m' : ManagedHeap) : m ≈ m' → m = m' := by
  obtain ⟨h, al⟩ := m; obtain ⟨h', al'⟩ := m'
  rintro ⟨Hh, Hal⟩
  exact Prod.ext (funext Hh) (funext Hal)

/-- First-fit search on an immutable snapshot: every rejected candidate is a silent guard; only
success changes the heap. Returns `(base, (heap', aux))`. -/
def alloc_search {F B : Effect.{0}} {Sig : Type} (h : Heap) (size candidate : Nat) (aux : Sig) :
    CTree F B (Nat × (Heap × Sig)) :=
  match size with
  | 0 => .stuck
  | _ + 1 =>
    if block_freeb h candidate size then pure (candidate, (hunion (hblock candidate size) h, aux))
    else .guard (alloc_search h size (candidate + 1) aux)
partial_fixpoint

/-- The checked heap handler. The state is `((h, allocs), aux)`: data heap, live extents and
auxiliary state. Allocation reuses the searched heap and records the extent. -/
def heap_handler {F B : Effect.{0}} {Sig : Type} :
    (e : heapE.I) → StateT (ManagedHeap × Sig) (CTree F B) (heapE.O e)
  | .read a => fun s =>
    match s.1.1 a with
    | some v => pure (v, s)
    | none => .stuck
  | .write a v => fun s =>
    match s.1.1 a with
    | some _ => pure (⟨⟩, ((upd s.1.1 a v, s.1.2), s.2))
    | none => .stuck
  | .alloc size => fun s =>
    alloc_search s.1.1 size 1 s.2 >>= fun r =>
      pure (r.1, ((r.2.1, upd s.1.2 r.1 size), r.2.2))
  | .free base => fun s =>
    match managed_free s.1 base with
    | some memory' => pure (⟨⟩, (memory', s.2))
    | none => .stuck
  | .cas a expected desired => fun s =>
    match s.1.1 a with
    | none => .stuck
    | some current =>
      if current = expected then pure (true, ((upd s.1.1 a desired, s.1.2), s.2))
      else pure (false, s)

/-- Observe successful mutations only (write, allocation, successful CAS, nonzero free). -/
def heap_mutation_obs {Sig : Type} :
    (e : heapE.I) → heapE.O e → ManagedHeap × Sig → Option ManagedHeap
  | .write .., _, post => some post.1
  | .alloc _, _, post => some post.1
  | .cas .., success, post => match (success : Bool) with
    | true => some post.1
    | false => none
  | .free base, _, post => match base with
    | 0 => none
    | _ + 1 => some post.1
  | .read _, _, _ => none

/-- The instrumented heap handler: logs a snapshot of the memory after each successful mutation. -/
def heap_handlerW {W : Type} {B : Effect.{0}} {Sig : Type} (snapshot : ManagedHeap → W) :
    (e : heapE.I) → StateT (ManagedHeap × Sig) (ctreeW W B) (heapE.O e) :=
  h_instr (heap_handler (F := void1)) fun e r post => (heap_mutation_obs e r post).map snapshot

/-! ## Raw handler equations -/

section HandlerEquations
variable {F B : Effect.{0}} {Sig : Type}

theorem heap_handler_rd_some (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat) :
    h a = some v →
    heap_handler (F := F) (B := B) (.read a) ((h, allocs), aux) = pure (v, ((h, allocs), aux)) :=
  fun H => by simp [heap_handler, H]

theorem heap_handler_rd_none (a : Nat) (h allocs : Heap) (aux : Sig) :
    h a = none → heap_handler (F := F) (B := B) (.read a) ((h, allocs), aux) = .stuck :=
  fun H => by simp [heap_handler, H]

theorem heap_handler_wr_some (a : Nat) (h allocs : Heap) (aux : Sig) (v w : Nat) :
    h a = some w →
    heap_handler (F := F) (B := B) (.write a v) ((h, allocs), aux) =
      pure (⟨⟩, ((upd h a v, allocs), aux)) :=
  fun H => by simp [heap_handler, H]

theorem heap_handler_wr_none (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat) :
    h a = none → heap_handler (F := F) (B := B) (.write a v) ((h, allocs), aux) = .stuck :=
  fun H => by simp [heap_handler, H]

theorem heap_handler_cas_success (a expected desired : Nat) (h allocs : Heap) (aux : Sig) :
    h a = some expected →
    heap_handler (F := F) (B := B) (.cas a expected desired) ((h, allocs), aux) =
      pure (true, ((upd h a desired, allocs), aux)) :=
  fun H => by simp [heap_handler, H]

theorem heap_handler_cas_failure (a expected desired current : Nat) (h allocs : Heap) (aux : Sig) :
    h a = some current → current ≠ expected →
    heap_handler (F := F) (B := B) (.cas a expected desired) ((h, allocs), aux) =
      pure (false, ((h, allocs), aux)) :=
  fun H N => by simp [heap_handler, H, N]

theorem heap_handler_cas_missing (a expected desired : Nat) (h allocs : Heap) (aux : Sig) :
    h a = none →
    heap_handler (F := F) (B := B) (.cas a expected desired) ((h, allocs), aux) = .stuck :=
  fun H => by simp [heap_handler, H]

/-- A successful free releases exactly the recorded block. -/
theorem heap_handler_free (base : Nat) (memory memory' : ManagedHeap) (aux : Sig) :
    managed_free memory base = some memory' →
    heap_handler (F := F) (B := B) (.free base) (memory, aux) = pure (⟨⟩, (memory', aux)) :=
  fun H => by simp [heap_handler, H]

/-- Interior-pointer, unknown-base and double frees are faults. -/
theorem heap_handler_free_invalid (base : Nat) (memory : ManagedHeap) (aux : Sig) :
    managed_free memory base = none →
    heap_handler (F := F) (B := B) (.free base) (memory, aux) = .stuck :=
  fun H => by simp [heap_handler, H]

end HandlerEquations

/-! ## Allocation search -/

section AllocSearch
variable {F B : Effect.{0}} {Sig : Type}

theorem unfold_alloc_search (h : Heap) (size candidate : Nat) (aux : Sig) :
    alloc_search (F := F) (B := B) h size candidate aux =
      match size with
      | 0 => .stuck
      | _ + 1 =>
        if block_freeb h candidate size
        then pure (candidate, (hunion (hblock candidate size) h, aux))
        else .guard (alloc_search h size (candidate + 1) aux) := by
  rw [alloc_search.eq_def]

/-- The search from `start` is exactly `base - start` guards before the first fit `base`. -/
theorem alloc_search_guards (h : Heap) (size start base : Nat) (aux : Sig) :
    0 < size → start ≤ base → block_free h base size →
    (∀ j, start ≤ j → j < base → ¬ block_free h j size) →
    alloc_search (F := F) (B := B) h size start aux =
      guards (base - start) (pure (base, (hunion (hblock base size) h, aux))) := by
  intro Pos L Free First
  obtain ⟨size, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
  generalize D : base - start = distance
  induction distance generalizing start with
  | zero =>
    obtain rfl : start = base := by omega
    rw [unfold_alloc_search, (block_freeb_spec _ _ _).2 Free]; rfl
  | succ distance ih =>
    have Test : block_freeb h start (size + 1) = false := by
      cases T : block_freeb h start (size + 1)
      · rfl
      · exact absurd ((block_freeb_spec _ _ _).1 T) (First start (Nat.le_refl _) (by omega))
    rw [unfold_alloc_search]
    simp only [Test, Bool.false_eq_true, ↓reduceIte, guards_succ]
    rw [ih (start + 1) (by omega) (fun j J B' => First j (by omega) B') (by omega)]

theorem alloc_search_first (h : Heap) (size start base : Nat) (aux : Sig) :
    0 < size → start ≤ base → block_free h base size →
    (∀ j, start ≤ j → j < base → ¬ block_free h j size) →
    alloc_search (F := F) (B := B) h size start aux ~
      (pure (base, (hunion (hblock base size) h, aux)) : CTree F B _) := by
  intro Pos L Free First
  rw [alloc_search_guards h size start base aux Pos L Free First]
  exact guards_sbisim _ _

/-- With no suitable block anywhere, the search silently diverges. -/
theorem alloc_search_no_space (h : Heap) (size start : Nat) (aux : Sig) :
    0 < size → (∀ j, start ≤ j → ¬ block_free h j size) →
    alloc_search (F := F) (B := B) h size start aux = CTree.spin := by
  intro Pos Full
  obtain ⟨size, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
  refine eq_coind (fun a b => ∃ start, (∀ j, start ≤ j → ¬ block_free h j (size + 1)) ∧
    a = alloc_search h (size + 1) start aux ∧ b = CTree.spin) ?_ _ _ ⟨start, Full, rfl, rfl⟩
  rintro _ _ ⟨start, Full, rfl, rfl⟩
  have Test : block_freeb h start (size + 1) = false := by
    cases T : block_freeb h start (size + 1)
    · rfl
    · exact absurd ((block_freeb_spec _ _ _).1 T) (Full start (Nat.le_refl _))
  rw [unfold_alloc_search]
  simp only [Test, Bool.false_eq_true, ↓reduceIte, unfold_guard, spin_unfold]
  exact .guard ⟨start + 1, fun j J => Full j (by omega), rfl, rfl⟩

theorem heap_handler_alloc_zero (h allocs : Heap) (aux : Sig) :
    heap_handler (F := F) (B := B) (.alloc 0) ((h, allocs), aux) = .stuck := by
  simp [heap_handler, unfold_alloc_search]

/-- First-fit allocation in raw form: exactly `base - 1` leading guards. -/
theorem heap_handler_alloc_first_guards (h allocs : Heap) (size base : Nat) (aux : Sig) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    heap_handler (F := F) (B := B) (.alloc size) ((h, allocs), aux) =
      guards (base - 1) (pure (base, (managed_alloc (h, allocs) base size, aux))) := by
  intro Pos B' Free First
  simp only [heap_handler]
  rw [alloc_search_guards h size 1 base aux Pos B' Free fun j J L => First j J L, bind_guards,
    pure_bind']
  rfl

/-- Malloc returns the first-fit base and records its extent. -/
theorem heap_handler_alloc_first (h allocs : Heap) (size base : Nat) (aux : Sig) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    heap_handler (F := F) (B := B) (.alloc size) ((h, allocs), aux) ~
      (pure (base, (managed_alloc (h, allocs) base size, aux)) : CTree F B _) := by
  intro Pos B' Free First
  rw [heap_handler_alloc_first_guards h allocs size base aux Pos B' Free First]
  exact guards_sbisim _ _

/-- A finite heap always admits a first-fit witness. -/
theorem heap_handler_alloc_finite (h allocs : Heap) (size : Nat) (aux : Sig) :
    heap_finite h → 0 < size →
    ∃ base, 0 < base ∧ block_free h base size ∧
      (∀ j, 0 < j → j < base → ¬ block_free h j size) ∧
      heap_handler (F := F) (B := B) (.alloc size) ((h, allocs), aux) ~
        (pure (base, (managed_alloc (h, allocs) base size, aux)) : CTree F B _) := by
  rintro ⟨B', Bound⟩ Pos
  have Search : ∀ distance start, max 1 B' = start + distance →
      ∃ base, start ≤ base ∧ block_free h base size ∧
        (∀ j, start ≤ j → j < base → ¬ block_free h j size) := by
    intro distance
    induction distance with
    | zero =>
      intro start D
      exact ⟨start, Nat.le_refl _, heap_bounded_block_free _ _ _ _ Bound (by omega),
        fun j J L => absurd L (by omega)⟩
    | succ distance ih =>
      intro start D
      cases T : block_freeb h start size
      · obtain ⟨base, L, F0, First⟩ := ih (start + 1) (by omega)
        refine ⟨base, by omega, F0, fun j J Lt Free => ?_⟩
        by_cases E : j = start
        · subst E; rw [(block_freeb_spec _ _ _).2 Free] at T; cases T
        · exact First j (by omega) Lt Free
      · exact ⟨start, Nat.le_refl _, (block_freeb_spec _ _ _).1 T,
          fun j J L => absurd L (by omega)⟩
  obtain ⟨base, L, F0, First⟩ := Search (max 1 B' - 1) 1 (by omega)
  exact ⟨base, by omega, F0, fun j J Lt => First j J Lt,
    heap_handler_alloc_first h allocs size base aux Pos (by omega) F0 fun j J Lt => First j J Lt⟩

theorem heap_handler_alloc_no_space (h allocs : Heap) (size : Nat) (aux : Sig) :
    0 < size → (∀ j, 0 < j → ¬ block_free h j size) →
    heap_handler (F := F) (B := B) (.alloc size) ((h, allocs), aux) = CTree.spin := by
  intro Pos Full
  simp only [heap_handler]
  rw [alloc_search_no_space h size 1 aux Pos fun j J => Full j J, spin_bind]

/-- The search followed by a continuation: `base - start` guards, then the continuation. -/
theorem alloc_search_bind_guards {X : Type} (h : Heap) (size start base : Nat) (aux : Sig)
    (k : Nat × (Heap × Sig) → CTree F B X) :
    0 < size → start ≤ base → block_free h base size →
    (∀ j, start ≤ j → j < base → ¬ block_free h j size) →
    (alloc_search h size start aux >>= k) =
      guards (base - start) (k (base, (hunion (hblock base size) h, aux))) := by
  intro Pos L Free First
  rw [alloc_search_guards h size start base aux Pos L Free First, bind_guards, pure_bind']

end AllocSearch

/-- One heap event under `interp_state` with a summed handler: the handler answers and the
continuation resumes behind one guard. -/
private theorem interp_heap_vis' {F G B : Effect.{0}} {S X : Type}
    (hh : (e : heapE.I) → StateT S (CTree F B) (heapE.O e))
    (other : (e : G.I) → StateT S (CTree F B) (G.O e)) (e : heapE.I)
    (k : heapE.O e → CTree (heapE ⊕ₑ G) B X) (s : S) :
    interp_state (h_sum hh other) (CTree.vis' (E₁ := heapE) e k) s =
      hh e s >>= fun xs => .guard (interp_state (h_sum hh other) (k xs.1) xs.2) :=
  interp_state_vis (h_sum hh other) (.inl e) k s

private theorem heap_trigger_bind {G B : Effect.{0}} {X : Type} (e : heapE.I)
    (k : heapE.O e → CTree (heapE ⊕ₑ G) B X) :
    (CTree.trigger' heapE e >>= k) = CTree.vis' (E₁ := heapE) e k := by
  simp [CTree.trigger']

/-! ## Lifting through `interp_state`

Adding another effect handler leaves the checked memory paths unchanged; `other` is arbitrary. -/

section HeapInterp
variable {F G B : Effect.{0}} {Sig : Type}
  (other : (e : G.I) → StateT (ManagedHeap × Sig) (CTree F B) (G.O e))

theorem interp_heap_rd {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat)
    (k : Nat → CTree (heapE ⊕ₑ G) B X) :
    h a = some v →
    interp_state (h_sum heap_handler other) (heap_read a >>= k) ((h, allocs), aux) ~
      interp_state (h_sum heap_handler other) (k v) ((h, allocs), aux) := by
  intro H
  rw [heap_read, heap_trigger_bind, interp_heap_vis', heap_handler_rd_some a h allocs aux v H,
    pure_bind']
  exact sb_guard _

theorem interp_heap_wr {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig) (v w : Nat)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    h a = some w →
    interp_state (h_sum heap_handler other) (heap_write a v >>= k) ((h, allocs), aux) ~
      interp_state (h_sum heap_handler other) (k ⟨⟩) ((upd h a v, allocs), aux) := by
  intro H
  rw [heap_write, heap_trigger_bind, interp_heap_vis', heap_handler_wr_some a h allocs aux v w H,
    pure_bind']
  exact sb_guard _

theorem interp_heap_wr_present {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    h a ≠ none →
    interp_state (h_sum heap_handler other) (heap_write a v >>= k) ((h, allocs), aux) ~
      interp_state (h_sum heap_handler other) (k ⟨⟩) ((upd h a v, allocs), aux) := by
  intro H
  obtain ⟨w, Hw⟩ := Option.ne_none_iff_exists'.1 H
  exact interp_heap_wr other a h allocs aux v w k Hw

theorem interp_heap_rd_stuck (a : Nat) (h allocs : Heap) (aux : Sig) :
    h a = none →
    interp_state (h_sum heap_handler other) (heap_read (E := heapE ⊕ₑ G) (B := B) a)
      ((h, allocs), aux) = .stuck := by
  intro H
  rw [heap_read, CTree.trigger', interp_heap_vis', heap_handler_rd_none a h allocs aux H,
    stuck_bind]

theorem interp_heap_wr_stuck (a v : Nat) (h allocs : Heap) (aux : Sig) :
    h a = none →
    interp_state (h_sum heap_handler other) (heap_write (E := heapE ⊕ₑ G) (B := B) a v)
      ((h, allocs), aux) = .stuck := by
  intro H
  rw [heap_write, CTree.trigger', interp_heap_vis', heap_handler_wr_none a h allocs aux v H,
    stuck_bind]

theorem interp_heap_cas_success {X : Type} (a expected desired : Nat) (h allocs : Heap) (aux : Sig)
    (k : Bool → CTree (heapE ⊕ₑ G) B X) :
    h a = some expected →
    interp_state (h_sum heap_handler other) (heap_cas a expected desired >>= k)
      ((h, allocs), aux) ~
      interp_state (h_sum heap_handler other) (k true) ((upd h a desired, allocs), aux) := by
  intro H
  rw [heap_cas, heap_trigger_bind, interp_heap_vis',
    heap_handler_cas_success a expected desired h allocs aux H, pure_bind']
  exact sb_guard _

theorem interp_heap_cas_failure {X : Type} (a expected desired current : Nat) (h allocs : Heap)
    (aux : Sig) (k : Bool → CTree (heapE ⊕ₑ G) B X) :
    h a = some current → current ≠ expected →
    interp_state (h_sum heap_handler other) (heap_cas a expected desired >>= k)
      ((h, allocs), aux) ~
      interp_state (h_sum heap_handler other) (k false) ((h, allocs), aux) := by
  intro H N
  rw [heap_cas, heap_trigger_bind, interp_heap_vis',
    heap_handler_cas_failure a expected desired current h allocs aux H N, pure_bind']
  exact sb_guard _

theorem interp_heap_cas_missing {X : Type} (a expected desired : Nat) (h allocs : Heap) (aux : Sig)
    (k : Bool → CTree (heapE ⊕ₑ G) B X) :
    h a = none →
    interp_state (h_sum heap_handler other) (heap_cas a expected desired >>= k)
      ((h, allocs), aux) ~ (CTree.stuck : CTree F B (X × (ManagedHeap × Sig))) := by
  intro H
  rw [heap_cas, heap_trigger_bind, interp_heap_vis',
    heap_handler_cas_missing a expected desired h allocs aux H, stuck_bind]
  exact sbisim_refl _

theorem interp_heap_alloc_zero (h allocs : Heap) (aux : Sig) :
    interp_state (h_sum heap_handler other) (heap_alloc (E := heapE ⊕ₑ G) (B := B) 0)
      ((h, allocs), aux) = .stuck := by
  rw [heap_alloc, CTree.trigger', interp_heap_vis', heap_handler_alloc_zero h allocs aux,
    stuck_bind]

theorem interp_heap_alloc_first {X : Type} (h allocs : Heap) (size base : Nat) (aux : Sig)
    (k : Nat → CTree (heapE ⊕ₑ G) B X) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    interp_state (h_sum heap_handler other) (heap_alloc size >>= k) ((h, allocs), aux) ~
      interp_state (h_sum heap_handler other) (k base)
        (managed_alloc (h, allocs) base size, aux) := by
  intro Pos B' Free First
  rw [heap_alloc, heap_trigger_bind, interp_heap_vis',
    heap_handler_alloc_first_guards h allocs size base aux Pos B' Free First, bind_guards,
    pure_bind']
  exact sbisim_trans (guards_sbisim _ _) (sb_guard _)

/-- A valid free continues with the released memory. -/
theorem interp_heap_free {X : Type} (base : Nat) (memory memory' : ManagedHeap) (aux : Sig)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    managed_free memory base = some memory' →
    interp_state (h_sum heap_handler other) (heap_free base >>= k) (memory, aux) ~
      interp_state (h_sum heap_handler other) (k ⟨⟩) (memory', aux) := by
  intro H
  rw [heap_free, heap_trigger_bind, interp_heap_vis', heap_handler_free base memory memory' aux H,
    pure_bind']
  exact sb_guard _

/-- An invalid free never runs its continuation. -/
theorem interp_heap_free_invalid {X : Type} (base : Nat) (memory : ManagedHeap) (aux : Sig)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    managed_free memory base = none →
    interp_state (h_sum heap_handler other) (heap_free base >>= k) (memory, aux) ~
      (CTree.stuck : CTree F B (X × (ManagedHeap × Sig))) := by
  intro H
  rw [heap_free, heap_trigger_bind, interp_heap_vis', heap_handler_free_invalid base memory aux H,
    stuck_bind]
  exact sbisim_refl _

end HeapInterp

/-! ## Observable checked-heap equations -/

section HandlerWEquations
variable {W : Type} {B : Effect.{0}} {Sig : Type} (snapshot : ManagedHeap → W)

theorem heap_handlerW_rd_some (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat) :
    h a = some v →
    heap_handlerW (B := B) snapshot (.read a) ((h, allocs), aux) =
      (pure (v, ((h, allocs), aux)) : ctreeW W B _) := by
  intro H
  simp [heap_handlerW, h_instr, heap_handler_rd_some a h allocs aux v H, heap_mutation_obs]

theorem heap_handlerW_rd_none (a : Nat) (h allocs : Heap) (aux : Sig) :
    h a = none →
    heap_handlerW (B := B) snapshot (.read a) ((h, allocs), aux) = (.stuck : ctreeW W B _) := by
  intro H
  simp [heap_handlerW, h_instr, heap_handler_rd_none a h allocs aux H]

theorem heap_handlerW_wr_some (a : Nat) (h allocs : Heap) (aux : Sig) (v old : Nat) :
    h a = some old →
    heap_handlerW (B := B) snapshot (.write a v) ((h, allocs), aux) =
      (log (snapshot (upd h a v, allocs)) >>= fun _ => pure (⟨⟩, ((upd h a v, allocs), aux)) :
        ctreeW W B _) := by
  intro H
  simp [heap_handlerW, h_instr, heap_handler_wr_some a h allocs aux v old H, heap_mutation_obs,
    log]

theorem heap_handlerW_wr_none (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat) :
    h a = none →
    heap_handlerW (B := B) snapshot (.write a v) ((h, allocs), aux) = (.stuck : ctreeW W B _) := by
  intro H
  simp [heap_handlerW, h_instr, heap_handler_wr_none a h allocs aux v H]

theorem heap_handlerW_cas_success (a expected desired : Nat) (h allocs : Heap) (aux : Sig) :
    h a = some expected →
    heap_handlerW (B := B) snapshot (.cas a expected desired) ((h, allocs), aux) =
      (log (snapshot (upd h a desired, allocs)) >>= fun _ =>
        pure (true, ((upd h a desired, allocs), aux)) : ctreeW W B _) := by
  intro H
  simp [heap_handlerW, h_instr, heap_handler_cas_success a expected desired h allocs aux H,
    heap_mutation_obs, log]

theorem heap_handlerW_cas_failure (a expected desired current : Nat) (h allocs : Heap)
    (aux : Sig) :
    h a = some current → current ≠ expected →
    heap_handlerW (B := B) snapshot (.cas a expected desired) ((h, allocs), aux) =
      (pure (false, ((h, allocs), aux)) : ctreeW W B _) := by
  intro H N
  simp [heap_handlerW, h_instr, heap_mutation_obs,
    heap_handler_cas_failure a expected desired current h allocs aux H N]

theorem heap_handlerW_cas_missing (a expected desired : Nat) (h allocs : Heap) (aux : Sig) :
    h a = none →
    heap_handlerW (B := B) snapshot (.cas a expected desired) ((h, allocs), aux) =
      (.stuck : ctreeW W B _) := by
  intro H
  simp [heap_handlerW, h_instr, heap_handler_cas_missing a expected desired h allocs aux H]

theorem heap_handlerW_free (base : Nat) (memory memory' : ManagedHeap) (aux : Sig) :
    managed_free memory base = some memory' →
    heap_handlerW (B := B) snapshot (.free base) (memory, aux) =
      (match base with
       | 0 => pure (⟨⟩, (memory', aux))
       | _ + 1 => log (snapshot memory') >>= fun _ => pure (⟨⟩, (memory', aux)) :
        ctreeW W B _) := by
  intro H
  cases base <;>
    simp [heap_handlerW, h_instr, heap_handler_free _ memory memory' aux H, heap_mutation_obs, log]

theorem heap_handlerW_free_invalid (base : Nat) (memory : ManagedHeap) (aux : Sig) :
    managed_free memory base = none →
    heap_handlerW (B := B) snapshot (.free base) (memory, aux) = (.stuck : ctreeW W B _) := by
  intro H
  simp [heap_handlerW, h_instr, heap_handler_free_invalid base memory aux H]

theorem heap_handlerW_alloc_zero (h allocs : Heap) (aux : Sig) :
    heap_handlerW (B := B) snapshot (.alloc 0) ((h, allocs), aux) = (.stuck : ctreeW W B _) := by
  simp [heap_handlerW, h_instr, heap_handler_alloc_zero h allocs aux]

theorem heap_handlerW_alloc_first_guards (h allocs : Heap) (size base : Nat) (aux : Sig) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    heap_handlerW (B := B) snapshot (.alloc size) ((h, allocs), aux) =
      (guards (base - 1)
        (log (snapshot (managed_alloc (h, allocs) base size)) >>= fun _ =>
          pure (base, (managed_alloc (h, allocs) base size, aux))) : ctreeW W B _) := by
  intro Pos Base Free First
  simp only [heap_handlerW, h_instr]
  rw [heap_handler_alloc_first_guards h allocs size base aux Pos Base Free First,
    translate_guards, bind_guards]
  simp [heap_mutation_obs, log]

theorem heap_handlerW_alloc_first (h allocs : Heap) (size base : Nat) (aux : Sig) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    heap_handlerW (B := B) snapshot (.alloc size) ((h, allocs), aux) ~
      (log (snapshot (managed_alloc (h, allocs) base size)) >>= fun _ =>
        pure (base, (managed_alloc (h, allocs) base size, aux)) : ctreeW W B _) := by
  intro Pos Base Free First
  rw [heap_handlerW_alloc_first_guards snapshot h allocs size base aux Pos Base Free First]
  exact guards_sbisim _ _

theorem heap_handlerW_alloc_no_space (h allocs : Heap) (size : Nat) (aux : Sig) :
    0 < size → (∀ j, 0 < j → ¬ block_free h j size) →
    heap_handlerW (B := B) snapshot (.alloc size) ((h, allocs), aux) = CTree.spin := by
  intro Pos Full
  simp only [heap_handlerW, h_instr]
  rw [heap_handler_alloc_no_space h allocs size aux Pos Full, translate_spin, spin_bind]

end HandlerWEquations

/-! ## Observable heap interpretation and continuations -/

section HeapWInterp
variable {W : Type} {G B : Effect.{0}} {Sig : Type} (snapshot : ManagedHeap → W)
  (other : (e : G.I) → StateT (ManagedHeap × Sig) (ctreeW W B) (G.O e))

theorem interp_heapW_rd {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat)
    (k : Nat → CTree (heapE ⊕ₑ G) B X) :
    h a = some v →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_read a >>= k) ((h, allocs), aux) ~
      interp_state (h_sum (heap_handlerW snapshot) other) (k v) ((h, allocs), aux) := by
  intro H
  rw [heap_read, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_rd_some snapshot a h allocs aux v H, pure_bind']
  exact sb_guard _

theorem interp_heapW_wr {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig) (v old : Nat)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    h a = some old →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_write a v >>= k)
      ((h, allocs), aux) ~
      (log (snapshot (upd h a v, allocs)) >>= fun _ =>
        interp_state (h_sum (heap_handlerW snapshot) other) (k ⟨⟩) ((upd h a v, allocs), aux)) := by
  intro H
  rw [heap_write, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_wr_some snapshot a h allocs aux v old H]
  simp only [log, vis_bind, pure_bind']
  exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

theorem interp_heapW_wr_present {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig) (v : Nat)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    h a ≠ none →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_write a v >>= k)
      ((h, allocs), aux) ~
      (log (snapshot (upd h a v, allocs)) >>= fun _ =>
        interp_state (h_sum (heap_handlerW snapshot) other) (k ⟨⟩) ((upd h a v, allocs), aux)) := by
  intro H
  obtain ⟨old, Hold⟩ := Option.ne_none_iff_exists'.1 H
  exact interp_heapW_wr snapshot other a h allocs aux v old k Hold

theorem interp_heapW_cas_success {X : Type} (a expected desired : Nat) (h allocs : Heap)
    (aux : Sig) (k : Bool → CTree (heapE ⊕ₑ G) B X) :
    h a = some expected →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_cas a expected desired >>= k)
      ((h, allocs), aux) ~
      (log (snapshot (upd h a desired, allocs)) >>= fun _ =>
        interp_state (h_sum (heap_handlerW snapshot) other) (k true)
          ((upd h a desired, allocs), aux)) := by
  intro H
  rw [heap_cas, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_cas_success snapshot a expected desired h allocs aux H]
  simp only [log, vis_bind, pure_bind']
  exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

theorem interp_heapW_cas_failure {X : Type} (a expected desired current : Nat) (h allocs : Heap)
    (aux : Sig) (k : Bool → CTree (heapE ⊕ₑ G) B X) :
    h a = some current → current ≠ expected →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_cas a expected desired >>= k)
      ((h, allocs), aux) ~
      interp_state (h_sum (heap_handlerW snapshot) other) (k false) ((h, allocs), aux) := by
  intro H N
  rw [heap_cas, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_cas_failure snapshot a expected desired current h allocs aux H N, pure_bind']
  exact sb_guard _

theorem interp_heapW_alloc_first {X : Type} (h allocs : Heap) (size base : Nat) (aux : Sig)
    (k : Nat → CTree (heapE ⊕ₑ G) B X) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_alloc size >>= k)
      ((h, allocs), aux) ~
      (log (snapshot (managed_alloc (h, allocs) base size)) >>= fun _ =>
        interp_state (h_sum (heap_handlerW snapshot) other) (k base)
          (managed_alloc (h, allocs) base size, aux)) := by
  intro Pos Base Free First
  rw [heap_alloc, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_alloc_first_guards snapshot h allocs size base aux Pos Base Free First,
    bind_guards]
  refine sbisim_trans (guards_sbisim _ _) ?_
  simp only [log, vis_bind, pure_bind']
  exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

theorem interp_heapW_free {X : Type} (base : Nat) (memory memory' : ManagedHeap) (aux : Sig)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    managed_free memory base = some memory' →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_free base >>= k) (memory, aux) ~
      match base with
      | 0 => interp_state (h_sum (heap_handlerW snapshot) other) (k ⟨⟩) (memory', aux)
      | _ + 1 => log (snapshot memory') >>= fun _ =>
          interp_state (h_sum (heap_handlerW snapshot) other) (k ⟨⟩) (memory', aux) := by
  intro H
  rw [heap_free, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_free snapshot base memory memory' aux H]
  cases base with
  | zero => simp only [pure_bind']; exact sb_guard _
  | succ n =>
    simp only [log, vis_bind, pure_bind']
    exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

theorem interp_heapW_rd_missing {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig)
    (k : Nat → CTree (heapE ⊕ₑ G) B X) :
    h a = none →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_read a >>= k) ((h, allocs), aux) ~
      (CTree.stuck : ctreeW W B (X × (ManagedHeap × Sig))) := by
  intro H
  rw [heap_read, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_rd_none snapshot a h allocs aux H, stuck_bind]
  exact sbisim_refl _

theorem interp_heapW_wr_missing {X : Type} (a v : Nat) (h allocs : Heap) (aux : Sig)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    h a = none →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_write a v >>= k)
      ((h, allocs), aux) ~ (CTree.stuck : ctreeW W B (X × (ManagedHeap × Sig))) := by
  intro H
  rw [heap_write, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_wr_none snapshot a h allocs aux v H, stuck_bind]
  exact sbisim_refl _

theorem interp_heapW_cas_missing {X : Type} (a expected desired : Nat) (h allocs : Heap)
    (aux : Sig) (k : Bool → CTree (heapE ⊕ₑ G) B X) :
    h a = none →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_cas a expected desired >>= k)
      ((h, allocs), aux) ~ (CTree.stuck : ctreeW W B (X × (ManagedHeap × Sig))) := by
  intro H
  rw [heap_cas, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_cas_missing snapshot a expected desired h allocs aux H, stuck_bind]
  exact sbisim_refl _

theorem interp_heapW_alloc_zero {X : Type} (h allocs : Heap) (aux : Sig)
    (k : Nat → CTree (heapE ⊕ₑ G) B X) :
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_alloc 0 >>= k) ((h, allocs), aux) ~
      (CTree.stuck : ctreeW W B (X × (ManagedHeap × Sig))) := by
  rw [heap_alloc, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_alloc_zero snapshot h allocs aux, stuck_bind]
  exact sbisim_refl _

theorem interp_heapW_free_invalid {X : Type} (base : Nat) (memory : ManagedHeap) (aux : Sig)
    (k : PUnit → CTree (heapE ⊕ₑ G) B X) :
    managed_free memory base = none →
    interp_state (h_sum (heap_handlerW snapshot) other) (heap_free base >>= k) (memory, aux) ~
      (CTree.stuck : ctreeW W B (X × (ManagedHeap × Sig))) := by
  intro H
  rw [heap_free, heap_trigger_bind, interp_heap_vis',
    heap_handlerW_free_invalid snapshot base memory aux H, stuck_bind]
  exact sbisim_refl _

end HeapWInterp

-- Not ported: the local Ltacs `heap_event`, `heapW_event`, `heapW_log` (replaced by the private
-- lemmas `interp_heap_vis'` and `heap_trigger_bind`). Added: `alloc_search_guards` (the guard-count
-- form of the search, from which `alloc_search_first`/`alloc_search_bind_guards` follow).

end Tisl
