/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.Frame
public import Logic.Yield.Nondeterministic
public import Logic.Utils.Vectors
public import Logic.Utils.Lists

/-!
# Owned two-lineage action machine: definitions, congruence and invariants

A forked CoCSL program after its outer fork is a pool whose slots are tagged with the lineage
(`child` or `parent`) that owns them. Each lineage owns a disjoint `ManagedHeap` reserved at the
fork (its immutable `anchor`), its current heap, emission count and last local observation; the
variable context is shared and read-only. `owned_step` is the scheduler made state-visible:
selection, source steps, yields, forks, returns and every successful primitive is one labelled
action of its owner. `project` keeps exactly one lineage, in its original order
(← `CTree/Interp/CSL/Owned.v`, lines 1-968).
-/

@[expose] public section
namespace Tisl.CSL
open CTree Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield
open ITree (Effect)

/-! ## Lineages -/

inductive Side
  | child
  | parent
  deriving DecidableEq, Repr

/-- Rocq `side_eq_dec`. -/
def side_eq_dec (a b : Side) : Decidable (a = b) := inferInstance

def side_eqb : Side → Side → Bool
  | .child, .child | .parent, .parent => true
  | _, _ => false

@[simp] theorem side_eqb_spec (a b : Side) : side_eqb a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [side_eqb]

@[simp] theorem side_eqb_self (a : Side) : side_eqb a a = true := by cases a <;> rfl

def other : Side → Side
  | .child => .parent
  | .parent => .child

/-- Overwrite one lineage's field. -/
def side_upd {A : Type _} (f : Side → A) (i : Side) (x : A) : Side → A :=
  fun j => if side_eqb j i then x else f j

/-- Keep one lineage's field and reset the other to `d`. -/
def side_only {A : Type _} (f : Side → A) (i : Side) (d : A) : Side → A :=
  fun j => if side_eqb j i then f j else d

/-! ## Pools and configurations -/

structure TaggedPool where
  size : Nat
  threads : Pool sE Bn size
  tags : Vector Side size
  focus : Option (Fin size)

structure OwnedCfg where
  pool : TaggedPool
  anchor : Side → ManagedHeap
  heap : Side → ManagedHeap
  ctx : Ctx
  base : Nat
  count : Side → Nat
  last : Side → Option (Indexed (Nat × Nat))

def mk_pool (n : Nat) (v : Pool sE Bn n) (g : Vector Side n) (f : Option (Fin n)) : TaggedPool :=
  { size := n, threads := v, tags := g, focus := f }

def set_pool (c : OwnedCfg) (p : TaggedPool) : OwnedCfg := { c with pool := p }

def set_heap (c : OwnedCfg) (i : Side) (m : ManagedHeap) : OwnedCfg :=
  { c with heap := side_upd c.heap i m }

/-- Emission advances only the owner's count; the remembered stamp is local. -/
def emit_cfg (c : OwnedCfg) (i : Side) (payload : Nat × Nat) : OwnedCfg :=
  { c with
    count := side_upd c.count i (c.count i + 1)
    last := side_upd c.last i (some (stamp payload (c.base + c.count i))) }

def global_count (c : OwnedCfg) : Nat := c.base + c.count .child + c.count .parent

/-- The state one lineage sees. -/
def local_state (i : Side) (c : OwnedCfg) : SSig := (c.heap i, (c.ctx, c.base + c.count i))

def joined_heap (c : OwnedCfg) : ManagedHeap := c.heap .child ⊎ c.heap .parent

/-- The state the original runner sees. -/
def joined_state (c : OwnedCfg) : SSig := (joined_heap c, (c.ctx, global_count c))

/-! ## Actions -/

/-- Rocq `OASelect | OAStep | OAYield | OAFork | OAReturn | OARead | OAWrite | OAFree base |
OACAS success | OAGet | OAEmit payload global_index`. -/
inductive OwnedKind
  | select
  | step
  | yield
  | fork
  | ret
  | read
  | write
  | free (base : Nat)
  | cas (success : Bool)
  | get
  | emit (payload : Nat × Nat) (global_index : Nat)
  deriving DecidableEq

structure OwnedAction where
  owner : Side
  action_kind : OwnedKind

def act (i : Side) (k : OwnedKind) : OwnedAction := ⟨i, k⟩

/-- Selection and source steps retain raw `tau`; successful mutations and emissions are visible. -/
def erase_action_label (a : OwnedAction) (post : ManagedHeap) :
    Option (Label (writerE (CSLObs (Nat × Nat)))) :=
  match a.action_kind with
  | .select | .step => some .tau
  | .write | .free (_ + 1) | .cas true =>
    some (.obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap post) ⟨⟩)
  | .emit p n => some (.obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp p n)) ⟨⟩)
  | _ => none

/-- A thread reaches the non-guard head `u` after finitely many guards. -/
def headed (t u : Thread sE Bn) : Prop := ∃ n, t = guards n u

/-- One primitive on the owner's local heap. Allocation has no rule; failed primitives have no
result. -/
def heap_prim (i : Side) (c : OwnedCfg) : (e : heapE.I) → Option (OwnedKind × heapE.O e × OwnedCfg)
  | .read a => match (c.heap i).1 a with
    | some v => some (.read, v, c)
    | none => none
  | .write a v => match (c.heap i).1 a with
    | some _ => some (.write, ⟨⟩, set_heap c i (upd (c.heap i).1 a v, (c.heap i).2))
    | none => none
  | .alloc _ => none
  | .free b => match managed_free (c.heap i) b with
    | some m' => some (.free b, ⟨⟩, set_heap c i m')
    | none => none
  | .cas a expected desired => match (c.heap i).1 a with
    | none => none
    | some current =>
      if current = expected
      then some (.cas true, true, set_heap c i (upd (c.heap i).1 a desired, (c.heap i).2))
      else some (.cas false, false, c)

/-- Context reads are local; context writes have no rule. -/
def ctx_prim (c : OwnedCfg) :
    (e : (stateE Ctx).I) → Option (OwnedKind × (stateE Ctx).O e × OwnedCfg)
  | .get => some (.get, c.ctx, c)
  | .put _ => none

def emit_prim (i : Side) (c : OwnedCfg) (p : (writerE (Nat × Nat)).I) :
    Option (OwnedKind × (writerE (Nat × Nat)).O p × OwnedCfg) :=
  some (.emit p (global_count c), ⟨⟩, emit_cfg c i p)

def prim_step (i : Side) (c : OwnedCfg) : (e : sE.I) → Option (OwnedKind × sE.O e × OwnedCfg)
  | .inl he => heap_prim i c he
  | .inr (.inl se) => ctx_prim c se
  | .inr (.inr we) => emit_prim i c we

/-- Selection from an unfocused nonempty pool. -/
def sel_step (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  ∃ j, a = act g[j] .select ∧ c' = set_pool c (mk_pool (n + 1) v g (some j))

/-- One action of the focused slot `j`, after its finite guard prefix. -/
def focus_step (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  (∃ t, headed v[j] (.step t) ∧ a = act g[j] .step ∧
    c' = set_pool c (mk_pool (n + 1) (v.set j t) g (some j))) ∨
  (∃ k : PUnit → Thread sE Bn, headed v[j] (.vis (E := CEff) (.inl ⟨⟩) k) ∧
    a = act g[j] .yield ∧ c' = set_pool c (mk_pool (n + 1) (v.set j (k ⟨⟩)) g none)) ∨
  (∃ k : Bool → Thread sE Bn, headed v[j] (.vis (E := CEff) (.inr (.inl ⟨⟩)) k) ∧
    a = act g[j] .fork ∧
    c' = set_pool c (mk_pool (n + 2) (Vector.cons (k true) (v.set j (k false)))
      (Vector.cons g[j] g) (some j.succ))) ∨
  (headed v[j] (pure ⟨⟩) ∧ a = act g[j] .ret ∧
    c' = set_pool c (mk_pool n (vector_remove v j) (vector_remove g j) none)) ∨
  (∃ (e : sE.I) (k : sE.O e → Thread sE Bn) (kind : OwnedKind) (y : sE.O e) (c1 : OwnedCfg),
    headed v[j] (.vis (E := CEff) (.inr (.inr e)) k) ∧
    prim_step g[j] c e = some (kind, y, c1) ∧ a = act g[j] kind ∧
    c' = set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j)))

def owned_step (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  match c.pool with
  | ⟨0, _, _, _⟩ => False
  | ⟨n + 1, v, g, none⟩ => sel_step c n v g a c'
  | ⟨n + 1, v, g, some j⟩ => focus_step c n v g j a c'

def owned_next (c c' : OwnedCfg) : Prop := ∃ a, owned_step c a c'

def silent_next (c d : OwnedCfg) : Prop :=
  ∃ a, owned_step c a d ∧ erase_action_label a (joined_heap d) = none

/-- Progress for an arbitrary transition relation (not the world-indexed Kripke `can_step`). -/
def hcan_step (R : OwnedCfg → OwnedCfg → Prop) (c : OwnedCfg) : Prop := ∃ c', R c c'

/-! ## Initial configurations -/

/-- The state after the outer fork: child slot first, parent focused. -/
def init_owned_threads (child parent : Thread sE Bn) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) : OwnedCfg :=
  let hs : Side → ManagedHeap := fun | .child => h | .parent => h'
  { pool := mk_pool 2 #v[child, parent] #v[.child, .parent] (some 1)
    anchor := hs, heap := hs, ctx := ctx, base := base
    count := fun _ => 0, last := fun _ => none }

/-- A standalone singleton lineage, focused or awaiting selection. -/
def init_local_thread (i : Side) (t : Thread sE Bn) (h : ManagedHeap) (ctx : Ctx) (base : Nat)
    (focused : Bool) : OwnedCfg :=
  let hs := side_only (fun _ => h) i managed_empty
  { pool := mk_pool 1 #v[t] #v[i] (if focused then some 0 else none)
    anchor := hs, heap := hs, ctx := ctx, base := base
    count := fun _ => 0, last := fun _ => none }

/-! ## Projection onto one lineage -/

abbrev fin_nat {n : Nat} (j : Fin n) : Nat := j.val

def tp_slots (p : TaggedPool) : List (Thread sE Bn × Side) := p.threads.toList.zip p.tags.toList

def owned_by (i : Side) (s : Thread sE Bn × Side) : Bool := side_eqb s.2 i

def proj_indices (i : Side) (p : TaggedPool) : List (Fin p.size) :=
  (fin_all p.size).filter fun j => side_eqb p.tags[j] i

def proj_slots (i : Side) (p : TaggedPool) : List (Thread sE Bn × Side) :=
  (proj_indices i p).map fun j => (p.threads[j], p.tags[j])

theorem tp_slots_indices (p : TaggedPool) :
    (fin_all p.size).map (fun j => (p.threads[j], p.tags[j])) = tp_slots p := by
  apply List.ext_getElem
  · simp [fin_all, tp_slots]
  · intro k h1 h2; simp [fin_all, tp_slots]

theorem proj_slots_filter (i : Side) (p : TaggedPool) :
    proj_slots i p = (tp_slots p).filter (owned_by i) := by
  rw [← tp_slots_indices, proj_slots, proj_indices, List.filter_map]; rfl

theorem tp_slots_nth_error (p : TaggedPool) (j : Fin p.size) :
    (tp_slots p)[fin_nat j]? = some (p.threads[j], p.tags[j]) :=
  nth_error_combine_some _ _ _ _ _ (vector_to_list_nth_error _ _) (vector_to_list_nth_error _ _)

theorem owned_by_self (i : Side) (t : Thread sE Bn) : owned_by i (t, i) = true := by
  simp [owned_by]

theorem proj_pos_lt (i : Side) (p : TaggedPool) (j : Fin p.size) (h : p.tags[j] = i) :
    (((tp_slots p).take (fin_nat j)).filter (owned_by i)).length < (proj_slots i p).length := by
  rw [proj_slots_filter]
  exact filter_firstn_lt _ _ _ _ (tp_slots_nth_error p j) (by simp [owned_by, h])

/-- An owned focus is rebased to its rank among its lineage; a foreign focus is cleared. -/
def proj_focus (i : Side) (p : TaggedPool) : Option (Fin (proj_slots i p).length) :=
  match p.focus with
  | some j => if h : p.tags[j] = i then some ⟨_, proj_pos_lt i p j h⟩ else none
  | none => none

def project_pool (i : Side) (p : TaggedPool) : TaggedPool where
  size := (proj_slots i p).length
  threads := Vector.map Prod.fst ⟨(proj_slots i p).toArray, by simp⟩
  tags := Vector.map Prod.snd ⟨(proj_slots i p).toArray, by simp⟩
  focus := proj_focus i p

def project (i : Side) (c : OwnedCfg) : OwnedCfg where
  pool := project_pool i c.pool
  anchor := side_only c.anchor i managed_empty
  heap := side_only c.heap i managed_empty
  ctx := c.ctx
  base := c.base
  count := side_only c.count i 0
  last := side_only c.last i none

/-- A global action as its owner sees it: only an emission's index changes, from the global to
the local count. -/
def project_action (i : Side) (c : OwnedCfg) (a : OwnedAction) : OwnedAction :=
  match a.action_kind with
  | .emit p _ => act a.owner (.emit p (c.base + c.count i))
  | k => act a.owner k

/-! ## Configuration equivalence -/

def slot_equ (s s' : Thread sE Bn × Side) : Prop := s.1 = s'.1 ∧ s.2 = s'.2

def focus_nat (p : TaggedPool) : Option Nat := p.focus.map fin_nat

def tp_equ (p q : TaggedPool) : Prop :=
  Forall2 slot_equ (tp_slots p) (tp_slots q) ∧ focus_nat p = focus_nat q

def owned_equ (c d : OwnedCfg) : Prop :=
  tp_equ c.pool d.pool ∧
  (∀ i, c.anchor i ≈ d.anchor i) ∧
  (∀ i, c.heap i ≈ d.heap i) ∧
  c.ctx = d.ctx ∧ c.base = d.base ∧
  (∀ i, c.count i = d.count i) ∧
  (∀ i, c.last i = d.last i)

/-- Predicates that factor through heaps, context, counters, last observations and
termination. -/
def same_view (c d : OwnedCfg) : Prop :=
  (∀ i, c.heap i ≈ d.heap i) ∧ c.ctx = d.ctx ∧ c.base = d.base ∧
  (∀ i, c.count i = d.count i) ∧ (∀ i, c.last i = d.last i) ∧
  (c.pool.size = 0 ↔ d.pool.size = 0)

/-! ## Ownership invariant -/

def support_le (m r : ManagedHeap) : Prop :=
  (∀ a, m.1 a ≠ none → r.1 a ≠ none) ∧ (∀ b, m.2 b ≠ none → r.2 b ≠ none)

def owned_wf (c : OwnedCfg) : Prop :=
  managed_wf (c.heap .child) ∧ managed_wf (c.heap .parent) ∧
  managed_wf (c.anchor .child) ∧ managed_wf (c.anchor .parent) ∧
  c.anchor .child # c.anchor .parent ∧
  support_le (c.heap .child) (c.anchor .child) ∧
  support_le (c.heap .parent) (c.anchor .parent) ∧
  c.heap .child # c.heap .parent

/-! ## Admission -/

/-- Components may not allocate (first fit is absolute) or write the shared context. -/
def component_event_ok : sE.I → Prop
  | .inl (.alloc _) => False
  | .inr (.inl (.put _)) => False
  | _ => True

/-- The address a pending primitive touches lies in reservation `r`. -/
def prim_addr_ok (r : ManagedHeap) : sE.I → Prop
  | .inl (.read a) | .inl (.write a _) | .inl (.cas a _ _) => r.1 a ≠ none
  | .inl (.free b) => b = 0 ∨ r.2 b ≠ none
  | .inl (.alloc _) => True
  | .inr _ => True

def focused_thread (p : TaggedPool) : Option (Thread sE Bn × Side) :=
  match p.focus with
  | some j => some (p.threads[j], p.tags[j])
  | none => none

/-- Every pending focused primitive of every reachable configuration stays inside `r`, whether
or not it would succeed. -/
def confined (r : ManagedHeap) (c0 : OwnedCfg) : Prop :=
  ∀ c, Star owned_next c0 c →
  ∀ (t : Thread sE Bn) (i : Side) (e : sE.I) (k : sE.O e → Thread sE Bn),
    focused_thread c.pool = some (t, i) →
    headed t (.vis (E := CEff) (.inr (.inr e)) k) →
    prim_addr_ok r e

/-- Returned states agree exactly except for extensional heap equality. -/
def owned_result_rel : PUnit × SSig → PUnit × SSig → Prop
  | (x, s), (x', s') => x = x' ∧ s.2 = s'.2 ∧ csl_memory s ≈ csl_memory s'

/-! ## Lineage-relative transitions -/

def own_next (i : Side) (c c' : OwnedCfg) : Prop := ∃ a, owned_step c a c' ∧ a.owner = i

def foreign_next (i : Side) (c c' : OwnedCfg) : Prop := ∃ a, owned_step c a c' ∧ a.owner ≠ i

/-- Finitely many foreign actions, then one action of lineage `i`. -/
def weak_next (i : Side) (c c' : OwnedCfg) : Prop :=
  ∃ mid, Star (foreign_next i) c mid ∧ own_next i mid c'

/-- Every outgoing action is foreign. -/
def StutterOnly (i : Side) (c : OwnedCfg) : Prop :=
  ∀ a c', owned_step c a c' → a.owner ≠ i

/-- The projection can move, and each of its moves is one global action of lineage `i`. -/
def OwnEnabled (i : Side) (c : OwnedCfg) : Prop :=
  hcan_step owned_next (project i c) ∧
  ∀ a' d', owned_step (project i c) a' d' →
    ∃ a c', owned_step c a c' ∧ a.owner = i ∧ project_action i c a = a' ∧
      owned_equ (project i c') d'

/-- Pending focused primitives of `c` lie in their owner's reservation. -/
def head_confined (c : OwnedCfg) : Prop :=
  ∀ (t : Thread sE Bn) (i : Side) (e : sE.I) (k : sE.O e → Thread sE Bn),
    focused_thread c.pool = some (t, i) →
    headed t (.vis (E := CEff) (.inr (.inr e)) k) →
    prim_addr_ok (c.anchor i) e

/-! ## Equivalence and transition congruence

Rocq `≅` is Lean `=`, so `slot_equ` is equality of slots and `owned_equ` collapses to equality of
configurations (`tp_equ_eq`, `owned_equ_eq`); the congruence lemmas below follow from it. -/

theorem Forall2_slot_refl (l : List (Thread sE Bn × Side)) : Forall2 slot_equ l l := by
  induction l with
  | nil => exact .nil
  | cons _ _ ih => exact .cons ⟨rfl, rfl⟩ ih

theorem Forall2_slot_sym (l l' : List (Thread sE Bn × Side)) :
    Forall2 slot_equ l l' → Forall2 slot_equ l' l := by
  intro h
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons ⟨hxy.1.symm, hxy.2.symm⟩ ih

theorem Forall2_slot_trans (l1 l2 l3 : List (Thread sE Bn × Side)) :
    Forall2 slot_equ l1 l2 → Forall2 slot_equ l2 l3 → Forall2 slot_equ l1 l3 := by
  intro h
  induction h generalizing l3 with
  | nil => exact id
  | cons hxy _ ih =>
    intro h3
    cases h3 with
    | cons hyz h3 => exact .cons ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩ (ih _ h3)

/-- `Forall2 slot_equ` is list equality. -/
theorem Forall2_slot_iff {l l' : List (Thread sE Bn × Side)} : Forall2 slot_equ l l' ↔ l = l' := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hxy _ ih => rw [Prod.ext hxy.1 hxy.2, ih]
  · rintro rfl; exact Forall2_slot_refl _

theorem owned_equ_Equivalence : Equivalence owned_equ where
  refl _ := ⟨⟨Forall2_slot_refl _, rfl⟩, fun _ => peq_refl _, fun _ => peq_refl _, rfl, rfl,
    fun _ => rfl, fun _ => rfl⟩
  symm := fun ⟨⟨hs, hf⟩, ea, eh, ex, eb, ec, el⟩ =>
    ⟨⟨Forall2_slot_sym _ _ hs, hf.symm⟩, fun i => peq_sym _ _ (ea i),
      fun i => peq_sym _ _ (eh i), ex.symm, eb.symm, fun i => (ec i).symm, fun i => (el i).symm⟩
  trans := fun ⟨⟨hs, hf⟩, ea, eh, ex, eb, ec, el⟩ ⟨⟨hs', hf'⟩, ea', eh', ex', eb', ec', el'⟩ =>
    ⟨⟨Forall2_slot_trans _ _ _ hs hs', hf.trans hf'⟩, fun i => peq_trans _ _ _ (ea i) (ea' i),
      fun i => peq_trans _ _ _ (eh i) (eh' i), ex.trans ex', eb.trans eb',
      fun i => (ec i).trans (ec' i), fun i => (el i).trans (el' i)⟩

theorem joined_heap_equ (c d : OwnedCfg) : owned_equ c d → joined_heap c = joined_heap d := by
  rintro ⟨-, -, eh, -⟩
  simp only [joined_heap, managed_heap_ext _ _ (eh .child), managed_heap_ext _ _ (eh .parent)]

theorem tp_slots_length (p : TaggedPool) : (tp_slots p).length = p.size := by simp [tp_slots]

theorem project_size_partition (c : OwnedCfg) :
    (project .child c).pool.size + (project .parent c).pool.size = c.pool.size := by
  show (proj_slots .child c.pool).length + (proj_slots .parent c.pool).length = c.pool.size
  rw [proj_slots_filter, proj_slots_filter, ← tp_slots_length]
  generalize tp_slots c.pool = l
  induction l with
  | nil => rfl
  | cons s l ih =>
    obtain ⟨t, i⟩ := s
    cases i <;> simp [List.filter_cons, owned_by, side_eqb] <;> omega

theorem projected_both_empty (c : OwnedCfg) (i : Side)
    (hi : (project i c).pool.size = 0) (ho : (project (other i) c).pool.size = 0) :
    c.pool.size = 0 := by
  have := project_size_partition c
  cases i <;> simp only [other] at ho <;> omega

theorem tp_equ_size (p q : TaggedPool) : tp_equ p q → p.size = q.size := by
  intro h; rw [← tp_slots_length p, ← tp_slots_length q]; exact Forall2_length h.1

theorem slots_Forall2_iff (n : Nat) (v w : Pool sE Bn n) (g g' : Vector Side n) :
    Forall2 slot_equ (v.toList.zip g.toList) (w.toList.zip g'.toList) ↔
      (∀ j : Fin n, v[j] = w[j]) ∧ g = g' := by
  rw [Forall2_slot_iff]
  constructor
  · intro h
    have := congrArg List.unzip h
    rw [List.unzip_zip (by simp), List.unzip_zip (by simp)] at this
    simp only [Prod.mk.injEq, Vector.toList_inj] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨fun _ => rfl, rfl⟩
  · rintro ⟨hv, rfl⟩
    obtain rfl : v = w := Vector.ext fun k hk => hv ⟨k, hk⟩
    rfl

theorem tp_equ_mk (n : Nat) (v : Pool sE Bn n) (g : Vector Side n) (f : Option (Fin n))
    (w : Pool sE Bn n) (g' : Vector Side n) (f' : Option (Fin n)) :
    tp_equ (mk_pool n v g f) (mk_pool n w g' f') ↔
      (∀ j : Fin n, v[j] = w[j]) ∧ g = g' ∧ f = f' := by
  have hf : f.map fin_nat = f'.map fin_nat ↔ f = f' := by
    cases f <;> cases f' <;> simp [Fin.val_inj]
  simp only [tp_equ, tp_slots, focus_nat, mk_pool, slots_Forall2_iff, hf, and_assoc]

/-- Equivalent tagged pools are equal. -/
theorem tp_equ_eq {p q : TaggedPool} (h : tp_equ p q) : p = q := by
  obtain ⟨n, v, g, f⟩ := p
  obtain ⟨n', w, g', f'⟩ := q
  obtain rfl : n = n' := tp_equ_size _ _ h
  obtain ⟨hv, rfl, rfl⟩ := (tp_equ_mk n v g f w g' f').1 h
  obtain rfl : v = w := Vector.ext fun k hk => hv ⟨k, hk⟩
  rfl

/-- Equivalent configurations are equal. -/
theorem owned_equ_eq {c d : OwnedCfg} (h : owned_equ c d) : c = d := by
  obtain ⟨p, a, hp, x, b, n, l⟩ := c
  obtain ⟨p', a', hp', x', b', n', l'⟩ := d
  obtain ⟨ep, ea, eh, ex, eb, ec, el⟩ := h
  dsimp only at ep ea eh ex eb ec el
  subst ex eb
  obtain rfl := tp_equ_eq ep
  obtain rfl : a = a' := funext fun i => managed_heap_ext _ _ (ea i)
  obtain rfl : hp = hp' := funext fun i => managed_heap_ext _ _ (eh i)
  obtain rfl : n = n' := funext ec
  obtain rfl : l = l' := funext el
  rfl

theorem set_pool_equ (c d : OwnedCfg) (p q : TaggedPool) :
    owned_equ c d → tp_equ p q → owned_equ (set_pool c p) (set_pool d q) :=
  fun ⟨_, h⟩ hp => ⟨hp, h⟩

theorem set_heap_equ (c d : OwnedCfg) (i : Side) (m m' : ManagedHeap) :
    owned_equ c d → m ≈ m' → owned_equ (set_heap c i m) (set_heap d i m') := by
  rintro ⟨ep, ea, eh, ex, eb, ec, el⟩ hm
  refine ⟨ep, ea, fun j => ?_, ex, eb, ec, el⟩
  show (if side_eqb j i then m else c.heap j) ≈ (if side_eqb j i then m' else d.heap j)
  cases side_eqb j i
  · exact eh j
  · exact hm

theorem emit_cfg_equ (c d : OwnedCfg) (i : Side) (p : Nat × Nat) :
    owned_equ c d → owned_equ (emit_cfg c i p) (emit_cfg d i p) := by
  rintro ⟨ep, ea, eh, ex, eb, ec, el⟩
  refine ⟨ep, ea, eh, ex, eb, fun j => ?_, fun j => ?_⟩ <;> simp [emit_cfg, side_upd, ec, el, eb]

/-- Primitives respect `owned_equ`: same kind and response, equivalent result. -/
theorem prim_step_equ (i : Side) (c d : OwnedCfg) (e : sE.I) (kind : OwnedKind) (y : sE.O e)
    (c1 : OwnedCfg) : owned_equ c d → prim_step i c e = some (kind, y, c1) →
    ∃ d1, prim_step i d e = some (kind, y, d1) ∧ owned_equ c1 d1 := by
  intro E H; obtain rfl := owned_equ_eq E; exact ⟨c1, H, owned_equ_Equivalence.refl _⟩

theorem headed_equ (t t' u : Thread sE Bn) : t = t' → headed t u → headed t' u := by
  rintro rfl h; exact h

/-- A finite head of a self-guarded tree is itself guarded: it cannot expose a primitive or a
return. -/
theorem self_guard_headed_guard (t u : Thread sE Bn) :
    t = .guard t → headed t u → ∃ v, u.unfold = .guard v := by
  rintro hself ⟨n, hhead⟩
  induction n generalizing u with
  | zero =>
    obtain rfl : u = t := hhead.symm
    exact ⟨u, (congrArg CTree.unfold hself).trans (unfold_guard u)⟩
  | succ n ih =>
    have := congrArg CTree.unfold (hself.symm.trans hhead)
    simp only [guards_succ, unfold_guard, CTreeF.guard.injEq] at this
    exact ih u this

theorem sel_step_equ (c d : OwnedCfg) (n : Nat) (v w : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (a : OwnedAction) (c' : OwnedCfg) :
    owned_equ c d → (∀ k : Fin (n + 1), v[k] = w[k]) → sel_step c n v g a c' →
    ∃ d', sel_step d n w g a d' ∧ owned_equ c' d' := by
  intro E hp S
  obtain rfl := owned_equ_eq E
  obtain rfl : v = w := Vector.ext fun k hk => hp ⟨k, hk⟩
  exact ⟨c', S, owned_equ_Equivalence.refl _⟩

theorem focus_step_equ (c d : OwnedCfg) (n : Nat) (v w : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (a : OwnedAction) (c' : OwnedCfg) :
    owned_equ c d → (∀ k : Fin (n + 1), v[k] = w[k]) → focus_step c n v g j a c' →
    ∃ d', focus_step d n w g j a d' ∧ owned_equ c' d' := by
  intro E hp S
  obtain rfl := owned_equ_eq E
  obtain rfl : v = w := Vector.ext fun k hk => hp ⟨k, hk⟩
  exact ⟨c', S, owned_equ_Equivalence.refl _⟩

theorem owned_step_equ (c d : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_equ c d → owned_step c a c' → ∃ d', owned_step d a d' ∧ owned_equ c' d' := by
  intro E S; obtain rfl := owned_equ_eq E; exact ⟨c', S, owned_equ_Equivalence.refl _⟩

theorem owned_next_equ (c d c' : OwnedCfg) :
    owned_equ c d → owned_next c c' → ∃ d', owned_next d d' ∧ owned_equ c' d' := by
  intro E S; obtain rfl := owned_equ_eq E; exact ⟨c', S, owned_equ_Equivalence.refl _⟩

theorem tp_slots_project (i : Side) (p : TaggedPool) :
    tp_slots (project_pool i p) = proj_slots i p := by
  simp only [tp_slots, project_pool, Vector.toList_map]
  show ((proj_slots i p).map Prod.fst).zip ((proj_slots i p).map Prod.snd) = _
  generalize proj_slots i p = l
  induction l with
  | nil => rfl
  | cons s l ih => simp [ih]

theorem Forall2_slot_filter (i : Side) (l l' : List (Thread sE Bn × Side)) :
    Forall2 slot_equ l l' →
    Forall2 slot_equ (l.filter (owned_by i)) (l'.filter (owned_by i)) := by
  intro h; obtain rfl := Forall2_slot_iff.1 h; exact Forall2_slot_refl _

theorem focus_nat_project (i : Side) (p : TaggedPool) :
    focus_nat (project_pool i p) =
      match p.focus with
      | some j =>
        if side_eqb p.tags[j] i
        then some (((tp_slots p).take (fin_nat j)).filter (owned_by i)).length
        else none
      | none => none := by
  obtain ⟨n, v, g, f⟩ := p
  cases f with
  | none => rfl
  | some j =>
    simp only [focus_nat, project_pool, proj_focus, Fin.getElem_fin]
    by_cases h : g[j.val] = i <;> simp [h]

theorem tp_equ_project (i : Side) (p q : TaggedPool) :
    tp_equ p q → tp_equ (project_pool i p) (project_pool i q) := by
  intro h; obtain rfl := tp_equ_eq h; exact ⟨Forall2_slot_refl _, rfl⟩

theorem project_equ (i : Side) (c d : OwnedCfg) :
    owned_equ c d → owned_equ (project i c) (project i d) := by
  intro h; obtain rfl := owned_equ_eq h; exact owned_equ_Equivalence.refl _

theorem managed_wf_peq (m m' : ManagedHeap) : m ≈ m' → managed_wf m → managed_wf m' :=
  fun h w => managed_heap_ext _ _ h ▸ w

theorem support_le_peq (m m' r r' : ManagedHeap) :
    m ≈ m' → r ≈ r' → support_le m r → support_le m' r' :=
  fun hm hr s => managed_heap_ext _ _ hm ▸ managed_heap_ext _ _ hr ▸ s

theorem owned_wf_equ (c d : OwnedCfg) : owned_equ c d → owned_wf c → owned_wf d :=
  fun h w => owned_equ_eq h ▸ w

/-! ## Initial configurations -/

theorem project_init_threads_child (child parent : Thread sE Bn) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) :
    owned_equ (project .child (init_owned_threads child parent h h' ctx base))
      (init_local_thread .child child h ctx base false) := by
  refine ⟨⟨?_, rfl⟩, fun i => ?_, fun i => ?_, rfl, rfl, fun i => ?_, fun i => ?_⟩
  · rw [Forall2_slot_iff]; show tp_slots (project_pool _ _) = _; rw [tp_slots_project]
    simp [proj_slots, proj_indices, fin_all, init_owned_threads, mk_pool, tp_slots, side_eqb,
      List.finRange_succ]; rfl
  all_goals cases i <;> first | exact peq_refl _ | rfl

theorem project_init_threads_parent (child parent : Thread sE Bn) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) :
    owned_equ (project .parent (init_owned_threads child parent h h' ctx base))
      (init_local_thread .parent parent h' ctx base true) := by
  refine ⟨⟨?_, rfl⟩, fun i => ?_, fun i => ?_, rfl, rfl, fun i => ?_, fun i => ?_⟩
  · rw [Forall2_slot_iff]; show tp_slots (project_pool _ _) = _; rw [tp_slots_project]
    simp [proj_slots, proj_indices, fin_all, init_owned_threads, mk_pool, tp_slots, side_eqb,
      List.finRange_succ]; rfl
  all_goals cases i <;> first | exact peq_refl _ | rfl

/-- An unfocused singleton's only action selects it. -/
theorem init_local_thread_select (i : Side) (p : Thread sE Bn) (h : ManagedHeap) (ctx : Ctx)
    (base : Nat) (a : OwnedAction) (d : OwnedCfg) :
    owned_step (init_local_thread i p h ctx base false) a d ↔
      a = act i .select ∧ d = init_local_thread i p h ctx base true := by
  show sel_step _ 0 #v[p] #v[i] a d ↔ _
  constructor
  · rintro ⟨j, rfl, rfl⟩; obtain rfl := fin1_eq j; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨0, rfl, rfl⟩

theorem support_le_refl (m : ManagedHeap) : support_le m m := ⟨fun _ h => h, fun _ h => h⟩

theorem init_owned_threads_wf (child parent : Thread sE Bn) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) : managed_wf h → managed_wf h' → h # h' →
    owned_wf (init_owned_threads child parent h h' ctx base) :=
  fun W W' D => ⟨W, W', W, W', D, support_le_refl h, support_le_refl h', D⟩

/-! ## One-step facts -/

theorem prim_step_facts (i : Side) (c : OwnedCfg) (e : sE.I) (kind : OwnedKind) (y : sE.O e)
    (c1 : OwnedCfg) : prim_step i c e = some (kind, y, c1) →
    kind ≠ .select ∧ c1.pool = c.pool ∧ c1.anchor = c.anchor ∧ c1.ctx = c.ctx ∧
      c1.base = c.base := by
  intro H
  rcases e with ((a | ⟨a, v⟩ | sz | b | ⟨a, ex, de⟩) | (_ | s) | p) <;>
    simp only [prim_step, heap_prim, ctx_prim, emit_prim] at H <;>
    (repeat' split at H) <;> cases H <;> simp [set_heap, emit_cfg]

theorem support_le_trans (m r s : ManagedHeap) :
    support_le m r → support_le r s → support_le m s :=
  fun ⟨a1, a2⟩ ⟨b1, b2⟩ => ⟨fun x h => b1 x (a1 x h), fun x h => b2 x (a2 x h)⟩

theorem support_le_disj (m m0 m1 : ManagedHeap) : support_le m m0 → m0 # m1 → m # m1 := by
  rintro ⟨S1, S2⟩ ⟨D1, D2⟩
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rcases D1 x with hx | hx
    · exact .inl (Decidable.byContradiction fun hne => S1 x hne hx)
    · exact .inr hx
  · rcases D2 x with hx | hx
    · exact .inl (Decidable.byContradiction fun hne => S2 x hne hx)
    · exact .inr hx

theorem owned_wf_heap (c : OwnedCfg) (i : Side) : owned_wf c → managed_wf (c.heap i) := by
  rintro ⟨W1, W2, -⟩; cases i <;> assumption

theorem set_heap_wf (c : OwnedCfg) (i : Side) (m : ManagedHeap) :
    owned_wf c → managed_wf m → support_le m (c.heap i) → owned_wf (set_heap c i m) := by
  rintro ⟨W1, W2, A1, A2, AD, S1, S2, D⟩ Wm Sm
  cases i
  · exact ⟨Wm, W2, A1, A2, AD, support_le_trans _ _ _ Sm S1, S2, support_le_disj _ _ _ Sm D⟩
  · exact ⟨W1, Wm, A1, A2, AD, S1, support_le_trans _ _ _ Sm S2,
      pdef_comm _ _ (support_le_disj _ _ _ Sm (pdef_comm _ _ D))⟩

theorem write_wf_support (m : ManagedHeap) (a v v0 : Nat) :
    managed_wf m → m.1 a = some v0 →
    managed_wf (upd m.1 a v, m.2) ∧ support_le (upd m.1 a v, m.2) m := by
  intro W Ha
  exact ⟨managed_write_preserves_wf _ _ _ _ W,
    fun x hx => (upd_dom _ _ _ x (by simp [Ha])).1 hx, fun _ h => h⟩

theorem free_wf_support (m m' : ManagedHeap) (b : Nat) :
    managed_wf m → managed_free m b = some m' → managed_wf m' ∧ support_le m' m := by
  intro W hf
  refine ⟨managed_free_preserves_wf _ _ _ W hf, ?_⟩
  simp only [managed_free] at hf
  split at hf
  · cases hf; exact support_le_refl _
  split at hf
  · cases hf
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simp only [hfree_block, hfree] at hx <;>
      split at hx <;> simp_all
  · cases hf

theorem prim_step_wf (i : Side) (c : OwnedCfg) (e : sE.I) (kind : OwnedKind) (y : sE.O e)
    (c1 : OwnedCfg) : owned_wf c → prim_step i c e = some (kind, y, c1) → owned_wf c1 := by
  intro W H
  rcases e with ((a | ⟨a, v⟩ | sz | b | ⟨a, ex, de⟩) | (_ | s) | p) <;>
    simp only [prim_step, heap_prim, ctx_prim, emit_prim] at H
  · split at H <;> cases H; exact W
  · split at H
    · rename_i v0 Ha; cases H
      obtain ⟨Wm, Sm⟩ := write_wf_support _ a v _ (owned_wf_heap _ i W) Ha
      exact set_heap_wf _ _ _ W Wm Sm
    · cases H
  · cases H
  · split at H
    · rename_i m' Hf; cases H
      obtain ⟨Wm, Sm⟩ := free_wf_support _ _ _ (owned_wf_heap _ i W) Hf
      exact set_heap_wf _ _ _ W Wm Sm
    · cases H
  · split at H
    · cases H
    · rename_i cur Ha
      split at H
      · cases H
        obtain ⟨Wm, Sm⟩ := write_wf_support _ a de _ (owned_wf_heap _ i W) Ha
        exact set_heap_wf _ _ _ W Wm Sm
      · cases H; exact W
  · cases H; exact W
  · cases H
  · cases H; exact W

-- Case analysis of one step `S` of the configuration `c`, which is destructed (Rocq `step_inv`).
-- Leaves six goals: selection, then the focused step/yield/fork/return/primitive cases.
local macro "step_inv " c:ident S:term : tactic => do
  let r := Lean.mkIdent `rfl -- the `rfl` pattern must not carry macro scopes
  `(tactic|
  (rcases $c:ident with ⟨⟨_ | n, v, g, _ | j⟩, an, he, cx, b, co, la⟩
   exact False.elim $S
   exact False.elim $S
   obtain ⟨j, $r:ident, $r:ident⟩ := $S
   rotate_left
   obtain ⟨t, Hh, $r:ident, $r:ident⟩ | ⟨k, Hh, $r:ident, $r:ident⟩ |
     ⟨k, Hh, $r:ident, $r:ident⟩ | ⟨Hh, $r:ident, $r:ident⟩ |
     ⟨e, k, kind, y, c1, Hh, Hs, $r:ident, $r:ident⟩ := $S
   rotate_right))

/-- Selection changes only the focus. -/
theorem owned_step_select_only (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step c a c' → a.action_kind = .select →
    c'.heap = c.heap ∧ c'.anchor = c.anchor ∧ c'.ctx = c.ctx ∧ c'.base = c.base ∧
      c'.count = c.count ∧ c'.last = c.last ∧ c'.pool.size = c.pool.size := by
  intro S K
  step_inv c S
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals first
    | (rename_i Hs; exact absurd K (prim_step_facts _ _ _ _ _ _ Hs).1)
    | cases K

theorem owned_step_wf (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_wf c → owned_step c a c' → owned_wf c' := by
  intro W S
  step_inv c S
  all_goals first
    | exact W
    | (rename_i c1 _ Hs; exact (show owned_wf c1 from prim_step_wf _ _ _ _ _ _ W Hs))

/-- Anchors, context and base never change. -/
theorem owned_step_frozen (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step c a c' → c'.anchor = c.anchor ∧ c'.ctx = c.ctx ∧ c'.base = c.base := by
  intro S
  step_inv c S
  all_goals first
    | exact ⟨rfl, rfl, rfl⟩
    | (rename_i Hs; exact (prim_step_facts _ _ _ _ _ _ Hs).2.2)

theorem owned_step_single_side (i : Side) (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    (∀ j : Fin c.pool.size, c.pool.tags[j] = i) → owned_step c a c' →
      ∀ j : Fin c'.pool.size, c'.pool.tags[j] = i := by
  intro Hi S
  step_inv c S
  all_goals try exact Hi
  · intro q
    cases q using Fin.cases with
    | zero => exact (Vector.getElem_cons_zero _ _).trans (Hi _)
    | succ q => exact (Vector.getElem_cons_succ _ _ _ _).trans (Hi q)
  · intro q
    exact (vector_remove_getElem _ _ q).trans (by split; exact Hi q.castSucc; exact Hi q.succ)

/-- Only the final return of a singleton pool reaches the empty pool. -/
theorem owned_step_terminal (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step c a c' → c'.pool.size = 0 → a.action_kind = .ret ∧ c.pool.size = 1 := by
  intro S Z
  step_inv c S
  all_goals first | exact absurd Z (Nat.succ_ne_zero _) | (subst Z; exact ⟨rfl, rfl⟩)

theorem owned_step_empty (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) :
    c.pool.size = 0 → ¬ owned_step c a c' := by
  obtain ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩ := c
  rintro (rfl : n = 0) S
  exact S

-- Not ported: Ltac `step_inv` (a local `step_inv` tactic macro that takes the configuration
-- explicitly instead). Rocq's `Local Lemma`
-- `owned_step_single_side` is public here (later Owned files may use it).

end Tisl.CSL
