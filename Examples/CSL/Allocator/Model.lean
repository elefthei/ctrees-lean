/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Mod
public import Logic.Utils.Execution
public import Logic.Yield.Execution
public import Examples.CSL.Queue.Representation
public import Examples.CSL.Allocator.Layout

/-!
# The allocator's turn model and ownership invariant

One selected source segment per actor, ending at its first yield, as a partial transition `turn`
on an explicit model state; the ownership view (`allocator_view`) with its ghost lists, the
transition completeness theorem `turn_view_complete`, and the two `Utils.Execution`
instantiations (← `examples/CSL/Allocator/Model.v`).
-/

@[expose] public section
namespace Examples.CSL.Allocator.Model
open Tisl Tisl.Heap Tisl.CSL Examples.CSL.Allocator.Layout

inductive Actor | Owner | Remote0 | Remote1
  deriving DecidableEq

inductive owner_pc | ORead | OCAS (old : Nat) | ODrain | OOffer (client : Bool)
  deriving DecidableEq

inductive remote_pc | RPoll | RRead (block : Nat) | RLink (block old : Nat) | RCAS (block old : Nat)
  deriving DecidableEq

open Actor owner_pc remote_pc

structure AState where
  aheap : Heap
  aallocs : AllocationTable
  acount : Nat
  owner_state : owner_pc
  remote0_state : remote_pc
  remote1_state : remote_pc

/-- One selected source segment, ending at its first yield. The helpers below only assemble this
example's result; missing checked cells fault. -/
def turn (base : Nat) (who : Actor) (s : AState) :
    Option (AState × List (CSLObs (Nat × Nat))) :=
  let finish (h : Heap) (op : owner_pc) (r0 r1 : remote_pc) (heaps : List ManagedHeap)
      (event : Option (Nat × Nat)) :=
    some ({ aheap := h, aallocs := s.aallocs,
            acount := match event with | none => s.acount | some _ => s.acount + 1,
            owner_state := op, remote0_state := r0, remote1_state := r1 },
          heaps.map CSLObs.heap ++ match event with
            | none => []
            | some (tag, block) => [CSLObs.emit (stamp (tag, block) s.acount)])
  let own pc h heaps event := finish h pc s.remote0_state s.remote1_state heaps event
  let remote (client : Bool) :=
    let pc := if client then s.remote1_state else s.remote0_state
    let done pc h heaps event :=
      if client then finish h s.owner_state s.remote0_state pc heaps event
      else finish h s.owner_state pc s.remote1_state heaps event
    match pc with
    | RPoll =>
      match s.aheap (mailbox base client) with
      | none => none
      | some block =>
        if block == 0 then done RPoll s.aheap [] none
        else
          let h := upd s.aheap (mailbox base client) 0
          match h (block + 1) with
          | none => none
          | some _ =>
            let h' := upd h (block + 1) (if client then 2 else 1)
            done (RRead block) h' [(h, s.aallocs), (h', s.aallocs)] none
    | RRead block =>
      match s.aheap (remote_head base) with
      | none => none
      | some old => done (RLink block old) s.aheap [] none
    | RLink block old =>
      match s.aheap block with
      | none => none
      | some _ =>
        let h := upd s.aheap block old
        done (RCAS block old) h [(h, s.aallocs)] none
    | RCAS block old =>
      match s.aheap (remote_head base) with
      | none => none
      | some current =>
        if current == old then
          let h := upd s.aheap (remote_head base) block
          done RPoll h [(h, s.aallocs)] (some (tag_retire, block))
        else done (RRead block) s.aheap [] (some (tag_retry, block))
  match who with
  | Remote0 => remote false
  | Remote1 => remote true
  | Owner =>
    match s.owner_state with
    | ORead =>
      match s.aheap (remote_head base) with
      | none => none
      | some old => own (OCAS old) s.aheap [] none
    | OCAS old =>
      match s.aheap (remote_head base) with
      | none => none
      | some current =>
        if current == old then
          let h := upd s.aheap (remote_head base) 0
          match h (drain_head base) with
          | none => none
          | some _ =>
            let h' := upd h (drain_head base) old
            own ODrain h' [(h, s.aallocs), (h', s.aallocs)] none
        else own ORead s.aheap [] none
    | ODrain =>
      match s.aheap (drain_head base) with
      | none => none
      | some block =>
        if block == 0 then own (OOffer false) s.aheap [] none
        else
          match s.aheap block, s.aheap (local_head base) with
          | some next, some lcl =>
            let h1 := upd s.aheap block lcl
            let h2 := upd h1 (local_head base) block
            let h3 := upd h2 (drain_head base) next
            own ODrain h3 [(h1, s.aallocs), (h2, s.aallocs), (h3, s.aallocs)]
              (some (tag_reclaim, block))
          | _, _ => none
    | OOffer client =>
      let next := if client then ORead else OOffer true
      match s.aheap (mailbox base client) with
      | none => none
      | some offered =>
        if offered == 0 then
          match s.aheap (local_head base) with
          | none => none
          | some block =>
            if block == 0 then own next s.aheap [] none
            else
              match s.aheap block with
              | none => none
              | some successor =>
                let h1 := upd s.aheap (local_head base) successor
                let h2 := upd h1 (mailbox base client) block
                own next h2 [(h1, s.aallocs), (h2, s.aallocs)] (some (tag_alloc, block))
        else own next s.aheap [] none

/-! ### Phase equations of `turn` (Lean-only)

One equation per source segment; every concrete replay below goes through these. -/

def remote_pc_of (client : Bool) (s : AState) : remote_pc :=
  if client then s.remote1_state else s.remote0_state

def set_remote_pc (client : Bool) (pc : remote_pc) (s : AState) : AState :=
  if client then { s with remote1_state := pc } else { s with remote0_state := pc }

def remote_actor (client : Bool) : Actor := if client then Remote1 else Remote0

theorem turn_remote_poll_empty (base : Nat) (client : Bool) (s : AState) :
    remote_pc_of client s = RPoll → s.aheap (mailbox base client) = some 0 →
    turn base (remote_actor client) s = some (s, []) := by
  intro h1 h2
  cases client <;> cases s <;> simp_all [turn, remote_pc_of, remote_actor]

theorem turn_remote_poll_pickup (base : Nat) (client : Bool) (s : AState) (block v : Nat) :
    remote_pc_of client s = RPoll → s.aheap (mailbox base client) = some block →
    block ≠ 0 → upd s.aheap (mailbox base client) 0 (block + 1) = some v →
    turn base (remote_actor client) s =
      some ({ set_remote_pc client (RRead block) s with
              aheap := upd (upd s.aheap (mailbox base client) 0) (block + 1)
                (if client then 2 else 1) },
        [.heap (upd s.aheap (mailbox base client) 0, s.aallocs),
         .heap (upd (upd s.aheap (mailbox base client) 0) (block + 1)
           (if client then 2 else 1), s.aallocs)]) := by
  intro h1 h2 h3 h4
  cases client <;> simp_all [turn, remote_pc_of, remote_actor, set_remote_pc]

theorem turn_remote_read (base : Nat) (client : Bool) (s : AState) (block old : Nat) :
    remote_pc_of client s = RRead block → s.aheap (remote_head base) = some old →
    turn base (remote_actor client) s = some (set_remote_pc client (RLink block old) s, []) := by
  intro h1 h2
  cases client <;> simp_all [turn, remote_pc_of, remote_actor, set_remote_pc]

theorem turn_remote_link (base : Nat) (client : Bool) (s : AState) (block old v : Nat) :
    remote_pc_of client s = RLink block old → s.aheap block = some v →
    turn base (remote_actor client) s =
      some ({ set_remote_pc client (RCAS block old) s with aheap := upd s.aheap block old },
        [.heap (upd s.aheap block old, s.aallocs)]) := by
  intro h1 h2
  cases client <;> simp_all [turn, remote_pc_of, remote_actor, set_remote_pc]

theorem turn_remote_cas_success (base : Nat) (client : Bool) (s : AState) (block old : Nat) :
    remote_pc_of client s = RCAS block old → s.aheap (remote_head base) = some old →
    turn base (remote_actor client) s =
      some ({ set_remote_pc client RPoll s with
              aheap := upd s.aheap (remote_head base) block, acount := s.acount + 1 },
        [.heap (upd s.aheap (remote_head base) block, s.aallocs),
         .emit (stamp (tag_retire, block) s.acount)]) := by
  intro h1 h2
  cases client <;> simp_all [turn, remote_pc_of, remote_actor, set_remote_pc]

theorem turn_remote_cas_retry (base : Nat) (client : Bool) (s : AState)
    (block old current : Nat) :
    remote_pc_of client s = RCAS block old → s.aheap (remote_head base) = some current →
    current ≠ old →
    turn base (remote_actor client) s =
      some ({ set_remote_pc client (RRead block) s with acount := s.acount + 1 },
        [.emit (stamp (tag_retry, block) s.acount)]) := by
  intro h1 h2 h3
  cases client <;> simp_all [turn, remote_pc_of, remote_actor, set_remote_pc]

theorem turn_owner_read (base : Nat) (s : AState) (old : Nat) :
    s.owner_state = ORead → s.aheap (remote_head base) = some old →
    turn base Owner s = some ({ s with owner_state := OCAS old }, []) := by
  intro h1 h2
  simp_all [turn]

theorem turn_owner_cas_success (base : Nat) (s : AState) (old v : Nat) :
    s.owner_state = OCAS old → s.aheap (remote_head base) = some old →
    upd s.aheap (remote_head base) 0 (drain_head base) = some v →
    turn base Owner s = some ({ s with
        owner_state := ODrain,
        aheap := upd (upd s.aheap (remote_head base) 0) (drain_head base) old },
      [.heap (upd s.aheap (remote_head base) 0, s.aallocs),
       .heap (upd (upd s.aheap (remote_head base) 0) (drain_head base) old, s.aallocs)]) := by
  intro h1 h2 h3
  simp_all [turn]

theorem turn_owner_cas_retry (base : Nat) (s : AState) (old current : Nat) :
    s.owner_state = OCAS old → s.aheap (remote_head base) = some current → current ≠ old →
    turn base Owner s = some ({ s with owner_state := ORead }, []) := by
  intro h1 h2 h3
  simp_all [turn]

theorem turn_owner_drain_empty (base : Nat) (s : AState) :
    s.owner_state = ODrain → s.aheap (drain_head base) = some 0 →
    turn base Owner s = some ({ s with owner_state := OOffer false }, []) := by
  intro h1 h2
  simp_all [turn]

theorem turn_owner_drain_block (base : Nat) (s : AState) (block next lcl : Nat) :
    s.owner_state = ODrain → s.aheap (drain_head base) = some block → block ≠ 0 →
    s.aheap block = some next → s.aheap (local_head base) = some lcl →
    turn base Owner s = some ({ s with
        aheap := upd (upd (upd s.aheap block lcl) (local_head base) block) (drain_head base)
          next,
        acount := s.acount + 1 },
      [.heap (upd s.aheap block lcl, s.aallocs),
       .heap (upd (upd s.aheap block lcl) (local_head base) block, s.aallocs),
       .heap (upd (upd (upd s.aheap block lcl) (local_head base) block) (drain_head base)
         next, s.aallocs),
       .emit (stamp (tag_reclaim, block) s.acount)]) := by
  intro h1 h2 h3 h4 h5
  simp_all [turn]

theorem turn_owner_offer_skip (base : Nat) (client : Bool) (s : AState) (offered : Nat) :
    s.owner_state = OOffer client → s.aheap (mailbox base client) = some offered →
    (offered ≠ 0 ∨ s.aheap (local_head base) = some 0) →
    turn base Owner s =
      some ({ s with owner_state := if client then ORead else OOffer true }, []) := by
  intro h1 h2 h3
  rcases h3 with h3 | h3 <;> simp_all [turn]

theorem turn_owner_offer_block (base : Nat) (client : Bool) (s : AState) (block succ : Nat) :
    s.owner_state = OOffer client → s.aheap (mailbox base client) = some 0 →
    s.aheap (local_head base) = some block → block ≠ 0 → s.aheap block = some succ →
    turn base Owner s = some ({ s with
        owner_state := if client then ORead else OOffer true,
        aheap := upd (upd s.aheap (local_head base) succ) (mailbox base client) block,
        acount := s.acount + 1 },
      [.heap (upd s.aheap (local_head base) succ, s.aallocs),
       .heap (upd (upd s.aheap (local_head base) succ) (mailbox base client) block,
         s.aallocs),
       .emit (stamp (tag_alloc, block) s.acount)]) := by
  intro h1 h2 h3 h4 h5
  simp_all [turn]

def initial_state (capacity c : Nat) : AState where
  aheap := page_heap 1 capacity hemp
  aallocs := upd hemp 1 (page_size capacity)
  acount := c
  owner_state := ORead
  remote0_state := RPoll
  remote1_state := RPoll

def held (pc : remote_pc) : List Nat :=
  match pc with
  | RPoll => []
  | RRead block | RLink block _ | RCAS block _ => [block]

def mailbox_nodes (block : Nat) : List Nat :=
  if block == 0 then [] else [block]

def cached_remote (base capacity : Nat) (h : Heap) (pc : remote_pc) : Prop :=
  match pc with
  | RPoll | RRead _ => True
  | RLink block old => (old = 0 ∨ old ∈ page_blocks base capacity) ∧ old ≠ block
  | RCAS block old =>
    (old = 0 ∨ old ∈ page_blocks base capacity) ∧ old ≠ block ∧ h block = some old

def backing (base capacity : Nat) (h : Heap) : Prop :=
  ∀ x, h x ≠ none ↔ base ≤ x ∧ x < base + page_size capacity

/-- The ownership view: the invariant body with its ghost lists exposed. `allocator_inv` is
exactly its existential closure; the ghost lists are proposition-level witnesses only. -/
def allocator_view (base capacity : Nat) (s : AState) (L R D : List Nat) : Prop :=
  0 < base ∧ backing base capacity s.aheap ∧
  ∃ m0 m1 : Nat,
    s.aheap (remote_head base) = some (R.headD 0) ∧
    s.aheap (local_head base) = some (L.headD 0) ∧
    s.aheap (drain_head base) = some (D.headD 0) ∧
    linked (fun a next => s.aheap a = some next) L 0 ∧
    linked (fun a next => s.aheap a = some next) R 0 ∧
    linked (fun a next => s.aheap a = some next) D 0 ∧
    s.aheap (mailbox base false) = some m0 ∧
    s.aheap (mailbox base true) = some m1 ∧
    List.Perm (L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++
      held s.remote0_state ++ held s.remote1_state) (page_blocks base capacity) ∧
    (match s.owner_state with | ODrain => True | _ => D = []) ∧
    (match s.owner_state with
     | OCAS old => old = 0 ∨ old ∈ page_blocks base capacity
     | _ => True) ∧
    cached_remote base capacity s.aheap s.remote0_state ∧
    cached_remote base capacity s.aheap s.remote1_state

def allocator_inv (base capacity : Nat) (s : AState) : Prop :=
  ∃ L R D, allocator_view base capacity s L R D

def state_equiv (s t : AState) : Prop :=
  heq s.aheap t.aheap ∧ heq s.aallocs t.aallocs ∧ s.acount = t.acount ∧
  s.owner_state = t.owner_state ∧ s.remote0_state = t.remote0_state ∧
  s.remote1_state = t.remote1_state

theorem initial_state_inv (capacity c : Nat) :
    allocator_inv 1 capacity (initial_state capacity c) := by
  refine ⟨page_blocks 1 capacity, [], [], by decide, fun x => page_heap_closed_dom 1 capacity x,
    0, 0, page_heap_remote _ _ _, page_heap_local_blocks _ _ _, page_heap_drain _ _ _,
    linked_of_splits _ _ _ fun pre b rest e => page_heap_link _ _ _ pre b rest e, trivial,
    trivial, page_heap_mailbox _ _ _ _, page_heap_mailbox _ _ _ _, ?_, rfl, trivial, trivial,
    trivial⟩
  simp [mailbox_nodes, held, initial_state]

/-- A turn contains only its successive post-mutation heaps, followed by at most one indexed
user emission. Only that final emission advances the counter. -/
theorem turn_log_shape (base : Nat) (who : Actor) (s t : AState)
    (logs : List (CSLObs (Nat × Nat))) :
    turn base who s = some (t, logs) →
    ∃ (heaps : List ManagedHeap) (payload : Option (Nat × Nat)),
      logs = heaps.map CSLObs.heap ++
        (match payload with | none => [] | some p => [CSLObs.emit (stamp p s.acount)]) ∧
      t.acount = match payload with | none => s.acount | some _ => s.acount + 1 := by
  obtain ⟨h, al, c, op, r0, r1⟩ := s
  intro T
  cases who <;> simp only [turn] at T <;>
    (repeat' split at T) <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at T <;>
    obtain ⟨rfl, rfl⟩ := T <;>
    first | exact ⟨_, none, rfl, rfl⟩ | exact ⟨_, some _, rfl, rfl⟩

theorem turn_emissions (base : Nat) (who : Actor) (s t : AState)
    (logs : List (CSLObs (Nat × Nat))) :
    turn base who s = some (t, logs) →
    (csl_emissions logs = [] ∧ t.acount = s.acount) ∨
    ∃ payload, csl_emissions logs = [stamp payload s.acount] ∧ t.acount = s.acount + 1 := by
  intro T
  obtain ⟨heaps, payload, rfl, hc⟩ := turn_log_shape base who s t logs T
  rw [csl_emissions_heap_prefix]
  cases payload with
  | none => exact .inl ⟨rfl, hc⟩
  | some p => exact .inr ⟨p, rfl, hc⟩

theorem turn_counter (base : Nat) (who : Actor) (s t : AState)
    (logs : List (CSLObs (Nat × Nat))) :
    turn base who s = some (t, logs) →
    (csl_emissions logs).length ≤ 1 ∧
    t.acount = s.acount + (csl_emissions logs).length ∧
    ∀ emission, emission ∈ csl_emissions logs → emission.index = s.acount := by
  intro T
  rcases turn_emissions base who s t logs T with ⟨hl, hc⟩ | ⟨p, hl, hc⟩ <;> rw [hl]
  · exact ⟨by simp, by simp [hc], by simp⟩
  · exact ⟨by simp, by simp [hc], by simp⟩

theorem state_equiv_refl (s : AState) : state_equiv s s :=
  ⟨heq_refl _, heq_refl _, rfl, rfl, rfl, rfl⟩

theorem state_equiv_sym (s t : AState) : state_equiv s t → state_equiv t s :=
  fun ⟨hh, ha, hc, ho, h0, h1⟩ =>
    ⟨heq_sym _ _ hh, heq_sym _ _ ha, hc.symm, ho.symm, h0.symm, h1.symm⟩

theorem state_equiv_trans (s t u : AState) :
    state_equiv s t → state_equiv t u → state_equiv s u :=
  fun ⟨hh, ha, hc, ho, h0, h1⟩ ⟨kh, ka, kc, ko, k0, k1⟩ =>
    ⟨heq_trans _ _ _ hh kh, heq_trans _ _ _ ha ka, hc.trans kc, ho.trans ko, h0.trans k0,
      h1.trans k1⟩

theorem state_equiv_equivalence : Equivalence state_equiv :=
  ⟨state_equiv_refl, state_equiv_sym _ _, state_equiv_trans _ _ _⟩

/-- `state_equiv` is equality: heaps are functions. -/
theorem state_equiv_eq (s t : AState) : state_equiv s t → s = t := by
  obtain ⟨h, al, c, op, r0, r1⟩ := s
  obtain ⟨k, al', c', op', r0', r1'⟩ := t
  rintro ⟨hh, ha, rfl, rfl, rfl, rfl⟩
  obtain rfl : h = k := funext hh
  obtain rfl : al = al' := funext ha
  rfl

/-- Both faults and successful turns are preserved (Rocq `Proper (eq ==> state_equiv ==>
Roption (RelProd state_equiv eq)) (turn base)`); no invariant or finiteness is assumed. -/
theorem turn_proper (base : Nat) (who : Actor) (s t : AState) :
    state_equiv s t →
    Option.Rel (fun p q => state_equiv p.1 q.1 ∧ p.2 = q.2) (turn base who s)
      (turn base who t) := by
  intro e
  obtain rfl := state_equiv_eq s t e
  cases turn base who s with
  | none => exact .none
  | some p => exact .some ⟨state_equiv_refl _, rfl⟩

/-- Physical source-pool order is `[client1, client0, owner]`. -/
def actor_of_slot (i : Fin 3) : Actor :=
  match i with
  | ⟨0, _⟩ => Remote1
  | ⟨1, _⟩ => Remote0
  | _ => Owner

def slot_of_actor (who : Actor) : Fin 3 :=
  match who with
  | Owner => 2
  | Remote0 => 1
  | Remote1 => 0

theorem actor_of_slot_of_actor (who : Actor) : actor_of_slot (slot_of_actor who) = who := by
  cases who <;> rfl

theorem slot_of_actor_of_slot (i : Fin 3) : slot_of_actor (actor_of_slot i) = i := by
  revert i; decide

theorem ai_cached_remote_frame (base capacity : Nat) (h h' : Heap) (pc : remote_pc) :
    cached_remote base capacity h pc → (∀ b, b ∈ held pc → h' b = h b) →
    cached_remote base capacity h' pc := by
  cases pc with
  | RPoll | RRead _ | RLink _ _ => exact fun H _ => H
  | RCAS b old => exact fun H hf => ⟨H.1, H.2.1, (hf b (.head _)).trans H.2.2⟩

theorem ai_backing_present (base capacity : Nat) (h : Heap) (x : Nat) :
    backing base capacity h → base ≤ x ∧ x < base + page_size capacity → ∃ v, h x = some v :=
  fun hback hr => Option.ne_none_iff_exists'.1 ((hback x).2 hr)

theorem ai_backing_upd (base capacity : Nat) (h : Heap) (a v : Nat) :
    backing base capacity h → base ≤ a ∧ a < base + page_size capacity →
    backing base capacity (upd h a v) :=
  fun hback ha x => (upd_dom h a v x ((hback a).2 ha)).trans (hback x)

/-! ## Ownership bookkeeping

The Rocq `ai_*` Ltacs are replaced by the geometry lemma `ai_block_bounds` (bounds and parity of a
page block, put in context per block), the frame lemma `linked_heap_frame`, and the macros
`ai_distinct` (address distinctness: metadata arithmetic, bounds/parity facts in context, or a
block-membership contradiction in context) and `ai_heap` (normalize `upd` lookups). -/

theorem ai_block_bounds (base capacity x : Nat) : x ∈ page_blocks base capacity →
    base + 5 ≤ x ∧ x + 2 ≤ base + 5 + 2 * capacity ∧ x % 2 = (base + 1) % 2 := by
  intro hx
  obtain ⟨j, hj, rfl⟩ := (page_blocks_in _ _ _).1 hx
  omega

theorem linked_heap_frame (h h' : Heap) (nodes : List Nat) (last : Nat) :
    (∀ a, a ∈ nodes → h' a = h a) →
    linked (fun a next => h a = some next) nodes last →
    linked (fun a next => h' a = some next) nodes last :=
  fun hf => linked_mono _ _ _ _ fun a _ ha e => (hf a ha).trans e

theorem ai_nodup_count {l : List Nat} (h : l.Nodup) (x : Nat) : l.count x ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    rw [List.count_cons]
    by_cases hx : a = x
    · subst hx
      have := List.count_eq_zero.2 h.1
      simp [this]
    · simp [hx, ih h.2]

theorem ai_perm_of_count {l l' p : List Nat} (h : ∀ x, l.count x = l'.count x) :
    l'.Perm p → l.Perm p :=
  (List.perm_iff_count.2 h).trans

theorem ai_ne_of_mem {a b : Nat} {l : List Nat} : a ∈ l -> b ∉ l -> a ≠ b :=
  fun ha hb e => hb (e ▸ ha)

macro "ai_distinct" : tactic => `(tactic| first
  | (simp only [ne_eq, remote_head, local_head, drain_head, mailbox, page_size,
      Bool.false_eq_true, ↓reduceIte]; first | done | omega)
  | omega
  | (apply ai_ne_of_mem; assumption; assumption)
  | (apply Ne.symm; apply ai_ne_of_mem; assumption; assumption))

macro "ai_heap" : tactic => `(tactic|
  simp (disch := ai_distinct) only [upd_eq, upd_neq, List.headD_nil, List.headD_cons])

macro "ai_interval" : tactic => `(tactic|
  (simp only [remote_head, local_head, drain_head, mailbox, page_size, Bool.false_eq_true,
    ↓reduceIte]; omega))

macro "ai_backing" : tactic => `(tactic|
  repeat (first | assumption | refine ai_backing_upd _ _ _ _ _ ?_ (by ai_interval)))

/-- Close a lookup in an updated heap, possibly by a hypothesis in context. -/
macro "ai_look" : tactic => `(tactic| first | (ai_heap; done) | (ai_heap; assumption) | assumption)

/-- Frame one chain member `a` (membership hypothesis `ha`) through the updates, using the block
bounds supplied by `hS`. -/
macro "ai_frame " hS:ident a:ident ha:ident : tactic => `(tactic|
  (obtain ⟨_, _, _⟩ := $hS $a (by simp only [List.mem_append, List.mem_cons, $ha:ident, true_or,
      or_true]); ai_heap))

/-! ## Ownership change of one turn

Every constructor is a projection of an actual executable turn: detach uses the current `R`,
and publication prepends to `R`. -/

def owner_after_offer (client : Bool) : owner_pc := if client then ORead else OOffer true

inductive ownership_transition :
    Actor → owner_pc → owner_pc → List (CSLObs (Nat × Nat)) →
    List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → Prop
  | ownership_read (L R : List Nat) :
    ownership_transition Owner ORead (OCAS (R.headD 0)) [] L R [] L R []
  | ownership_cas_fail (old : Nat) (L R : List Nat) :
    R.headD 0 ≠ old → ownership_transition Owner (OCAS old) ORead [] L R [] L R []
  | ownership_detach (L R : List Nat) (heaps : List ManagedHeap) :
    ownership_transition Owner (OCAS (R.headD 0)) ODrain (heaps.map CSLObs.heap) L R [] L [] R
  | ownership_drain_empty (L R : List Nat) :
    ownership_transition Owner ODrain (OOffer false) [] L R [] L R []
  | ownership_drain (L R : List Nat) (b : Nat) (D : List Nat) (idx : Nat)
      (heaps : List ManagedHeap) :
    ownership_transition Owner ODrain ODrain
      (heaps.map CSLObs.heap ++ [CSLObs.emit (stamp (tag_reclaim, b) idx)])
      L R (b :: D) (b :: L) R D
  | ownership_offer_empty (client : Bool) (L R : List Nat) :
    ownership_transition Owner (OOffer client) (owner_after_offer client) [] L R [] L R []
  | ownership_offer (client : Bool) (L R : List Nat) (b idx : Nat) (heaps : List ManagedHeap) :
    ownership_transition Owner (OOffer client) (owner_after_offer client)
      (heaps.map CSLObs.heap ++ [CSLObs.emit (stamp (tag_alloc, b) idx)]) (b :: L) R [] L R []
  | ownership_remote (who : Actor) (pc : owner_pc) (event : List (CSLObs (Nat × Nat)))
      (L R D : List Nat) :
    who ≠ Owner →
    (csl_emissions event = [] ∨ ∃ b idx, csl_emissions event = [stamp (tag_retry, b) idx]) →
    ownership_transition who pc pc event L R D L R D
  | ownership_publish (who : Actor) (pc : owner_pc) (L R D : List Nat) (b idx : Nat)
      (heaps : List ManagedHeap) :
    who ≠ Owner →
    ownership_transition who pc pc
      (heaps.map CSLObs.heap ++ [CSLObs.emit (stamp (tag_retire, b) idx)]) L R D L (b :: R) D

theorem ai_turn_intro {o : Option (AState × List (CSLObs (Nat × Nat)))}
    {V : AState → List Nat → List Nat → List Nat → Prop}
    {T : AState → List (CSLObs (Nat × Nat)) → List Nat → List Nat → List Nat → Prop} :
    (match o with
     | some (t, ev) => ∃ L' R' D', V t L' R' D' ∧ T t ev L' R' D'
     | none => False) →
    ∃ t ev L' R' D', o = some (t, ev) ∧ V t L' R' D' ∧ T t ev L' R' D' := by
  match o with
  | some (t, ev) => exact fun ⟨L', R', D', hv, ht⟩ => ⟨t, ev, L', R', D', rfl, hv, ht⟩
  | none => exact False.elim

open ownership_transition in
/-- Transition completeness: on the ownership view every turn succeeds, re-establishes the view,
and changes ownership by one constructor. -/
theorem turn_view_complete (base capacity : Nat) (who : Actor) (s : AState) (L R D : List Nat) :
    allocator_view base capacity s L R D →
    ∃ t event L' R' D',
      turn base who s = some (t, event) ∧
      allocator_view base capacity t L' R' D' ∧
      ownership_transition who s.owner_state t.owner_state event L R D L' R' D' := by
  obtain ⟨h, al, count, op, p0, p1⟩ := s
  rintro ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, CD, Hm0, Hm1, Hp, Hop, Ho, Hc0, Hc1⟩
  dsimp only at Hback Hr Hl Hd CL CR CD Hm0 Hm1 Hp Hop Ho Hc0 Hc1 ⊢
  have hS : ∀ x, x ∈ L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++ held p0 ++ held p1 →
      base + 5 ≤ x ∧ x + 2 ≤ base + 5 + 2 * capacity ∧ x % 2 = (base + 1) % 2 :=
    fun x hx => ai_block_bounds _ _ _ (Hp.subset hx)
  have hcnt : ∀ x, (L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++ held p0 ++
      held p1).count x ≤ 1 := fun x => by
    rw [Hp.count_eq]; exact ai_nodup_count (page_blocks_nodup _ _) x
  simp only [List.count_append] at hcnt
  cases who with
  | Owner =>
    cases op with
    | ORead =>
      obtain rfl : D = [] := Hop
      apply ai_turn_intro
      simp only [turn, Hr]
      refine ⟨L, R, [], ?_, ?_⟩
      · refine ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, trivial, Hm0, Hm1, Hp, rfl, ?_, Hc0, Hc1⟩
        rcases head_in_or_default 0 R with e | e
        · exact .inl e
        · exact .inr (Hp.subset (by simp only [List.mem_append, e, true_or, or_true]))
      · exact ownership_read L R
    | OCAS old =>
      obtain rfl : D = [] := Hop
      apply ai_turn_intro
      by_cases hc : R.headD 0 = old
      · subst hc
        simp (disch := ai_distinct) only [turn, Hr, Hd, upd_neq, beq_self_eq_true,
          ↓reduceIte, List.headD_nil, List.append_nil]
        refine ⟨L, [], R, ⟨Hbase, by ai_backing, m0, m1, by ai_look, by ai_look, by ai_look,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL, trivial,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR, by ai_look, by ai_look,
          ai_perm_of_count (fun x => by simp only [List.count_append, List.count_nil]; omega) Hp,
          trivial, trivial,
          ai_cached_remote_frame _ _ _ _ _ Hc0 (fun c hc => by ai_frame hS c hc),
          ai_cached_remote_frame _ _ _ _ _ Hc1 (fun c hc => by ai_frame hS c hc)⟩,
          ownership_detach L R _⟩
      · have hc' : (R.headD 0 == old) = false := beq_eq_false_iff_ne.2 hc
        simp only [turn, Hr, hc', Bool.false_eq_true, ↓reduceIte, List.append_nil]
        exact ⟨L, R, [], ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, trivial, Hm0, Hm1, Hp, rfl,
          trivial, Hc0, Hc1⟩, ownership_cas_fail old L R hc⟩
    | ODrain =>
      rcases D with _ | ⟨b, D⟩
      · apply ai_turn_intro
        simp only [turn, Hd, List.headD_nil, beq_self_eq_true, ↓reduceIte, List.append_nil]
        exact ⟨L, R, [], ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, trivial, Hm0, Hm1, Hp, rfl,
          trivial, Hc0, Hc1⟩, ownership_drain_empty L R⟩
      · obtain ⟨hbn, CD⟩ := CD
        obtain ⟨hb1, hb2, hb3⟩ := hS b (by simp only [List.mem_append, List.mem_cons, true_or,
          or_true])
        have hc := hcnt b
        simp only [List.count_cons, beq_self_eq_true, ↓reduceIte] at hc
        have nL : b ∉ L := List.count_eq_zero.1 (by omega)
        have nR : b ∉ R := List.count_eq_zero.1 (by omega)
        have nD : b ∉ D := List.count_eq_zero.1 (by omega)
        have n0 : b ∉ held p0 := List.count_eq_zero.1 (by omega)
        have n1 : b ∉ held p1 := List.count_eq_zero.1 (by omega)
        have hb0 : (b == 0) = false := beq_eq_false_iff_ne.2 (by omega)
        apply ai_turn_intro
        simp only [turn, Hd, List.headD_cons, hb0, Bool.false_eq_true, ↓reduceIte, hbn, Hl]
        refine ⟨b :: L, R, D, ⟨Hbase, by ai_backing, m0, m1, by ai_look, by ai_look, by ai_look,
          ⟨by ai_look, linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL⟩,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CD, by ai_look, by ai_look,
          ai_perm_of_count (fun x => by
            simp only [List.count_append, List.count_cons]; omega) Hp,
          trivial, trivial,
          ai_cached_remote_frame _ _ _ _ _ Hc0 (fun c hc => by ai_frame hS c hc),
          ai_cached_remote_frame _ _ _ _ _ Hc1 (fun c hc => by ai_frame hS c hc)⟩,
          ownership_drain L R b D count _⟩
    | OOffer client =>
      obtain rfl : D = [] := Hop
      cases client with
      | false =>
        by_cases hm : m0 = 0
        · subst hm
          rcases L with _ | ⟨b, L⟩
          · apply ai_turn_intro
            simp only [turn, Hm0, Hl, beq_self_eq_true, ↓reduceIte, List.headD_nil,
              Bool.false_eq_true, List.append_nil]
            exact ⟨[], R, [], ⟨Hbase, Hback, 0, m1, Hr, Hl, Hd, CL, CR, trivial, Hm0, Hm1, Hp, rfl,
              trivial, Hc0, Hc1⟩, ownership_offer_empty false [] R⟩
          · obtain ⟨hbn, CL⟩ := CL
            obtain ⟨hb1, hb2, hb3⟩ := hS b (by simp only [List.mem_append, List.mem_cons, true_or])
            have hb0 : (b == 0) = false := beq_eq_false_iff_ne.2 (by omega)
            apply ai_turn_intro
            simp only [turn, Hm0, Hl, List.headD_cons, beq_self_eq_true, hb0, ↓reduceIte,
              Bool.false_eq_true, hbn]
            refine ⟨L, R, [], ⟨Hbase, by ai_backing, b, m1, by ai_look, by ai_look, by ai_look,
              linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
              linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR, trivial,
              by ai_look, by ai_look,
              ai_perm_of_count (fun x => by
                simp only [List.count_append, List.count_cons, List.count_nil, mailbox_nodes, hb0,
                  beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]; omega) Hp,
              rfl, trivial,
              ai_cached_remote_frame _ _ _ _ _ Hc0 (fun c hc => by ai_frame hS c hc),
              ai_cached_remote_frame _ _ _ _ _ Hc1 (fun c hc => by ai_frame hS c hc)⟩,
              ownership_offer false L R b count _⟩
        · have hm' : (m0 == 0) = false := beq_eq_false_iff_ne.2 hm
          apply ai_turn_intro
          simp only [turn, Hm0, hm', Bool.false_eq_true, ↓reduceIte, List.append_nil]
          exact ⟨L, R, [], ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, trivial, Hm0, Hm1, Hp, rfl,
            trivial, Hc0, Hc1⟩, ownership_offer_empty false L R⟩
      | true =>
        by_cases hm : m1 = 0
        · subst hm
          rcases L with _ | ⟨b, L⟩
          · apply ai_turn_intro
            simp only [turn, Hm1, Hl, beq_self_eq_true, ↓reduceIte, List.headD_nil,
              List.append_nil]
            exact ⟨[], R, [], ⟨Hbase, Hback, m0, 0, Hr, Hl, Hd, CL, CR, trivial, Hm0, Hm1, Hp, rfl,
              trivial, Hc0, Hc1⟩, ownership_offer_empty true [] R⟩
          · obtain ⟨hbn, CL⟩ := CL
            obtain ⟨hb1, hb2, hb3⟩ := hS b (by simp only [List.mem_append, List.mem_cons, true_or])
            have hb0 : (b == 0) = false := beq_eq_false_iff_ne.2 (by omega)
            apply ai_turn_intro
            simp only [turn, Hm1, Hl, List.headD_cons, beq_self_eq_true, hb0, ↓reduceIte,
              Bool.false_eq_true, hbn]
            refine ⟨L, R, [], ⟨Hbase, by ai_backing, m0, b, by ai_look, by ai_look, by ai_look,
              linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
              linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR, trivial,
              by ai_look, by ai_look,
              ai_perm_of_count (fun x => by
                simp only [List.count_append, List.count_cons, List.count_nil, mailbox_nodes, hb0,
                  beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]; omega) Hp,
              rfl, trivial,
              ai_cached_remote_frame _ _ _ _ _ Hc0 (fun c hc => by ai_frame hS c hc),
              ai_cached_remote_frame _ _ _ _ _ Hc1 (fun c hc => by ai_frame hS c hc)⟩,
              ownership_offer true L R b count _⟩
        · have hm' : (m1 == 0) = false := beq_eq_false_iff_ne.2 hm
          apply ai_turn_intro
          simp only [turn, Hm1, hm', Bool.false_eq_true, ↓reduceIte, List.append_nil]
          exact ⟨L, R, [], ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, trivial, Hm0, Hm1, Hp, rfl,
            trivial, Hc0, Hc1⟩, ownership_offer_empty true L R⟩
  | Remote0 =>
    cases p0 with
    | RPoll =>
      by_cases hm : m0 = 0
      · subst hm
        apply ai_turn_intro
        simp only [turn, Hm0, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
        exact ⟨L, R, D, ⟨Hbase, Hback, 0, m1, Hr, Hl, Hd, CL, CR, CD, Hm0, Hm1, Hp, Hop, Ho, Hc0,
          Hc1⟩, ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
      · have hm' : (m0 == 0) = false := beq_eq_false_iff_ne.2 hm
        obtain ⟨hb1, hb2, hb3⟩ := hS m0 (by simp [mailbox_nodes, hm'])
        obtain ⟨v, hv⟩ := ai_backing_present base capacity h (m0 + 1) Hback
          (by simp only [page_size]; omega)
        apply ai_turn_intro
        simp (disch := ai_distinct) only [turn, Hm0, hm', Bool.false_eq_true, ↓reduceIte,
          upd_neq, hv]
        refine ⟨L, R, D, ⟨Hbase, by ai_backing, 0, m1, by ai_look, by ai_look, by ai_look,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CD, by ai_look, by ai_look,
          ai_perm_of_count (fun x => by
            simp only [List.count_append, mailbox_nodes, hm', beq_self_eq_true, ↓reduceIte,
              Bool.false_eq_true, held]; omega) Hp,
          Hop, Ho, trivial,
          ai_cached_remote_frame _ _ _ _ _ Hc1 (fun c hc => by ai_frame hS c hc)⟩,
          ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
    | RRead block =>
      obtain ⟨hb1, hb2, hb3⟩ := hS block (by simp [held])
      have hc := hcnt block
      simp only [held, List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hc
      have nR : block ∉ R := List.count_eq_zero.1 (by omega)
      apply ai_turn_intro
      simp only [turn, Hr]
      refine ⟨L, R, D, ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, CD, Hm0, Hm1, Hp, Hop, Ho,
        ⟨?_, ?_⟩, Hc1⟩, ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
      · rcases head_in_or_default 0 R with e | e
        · exact .inl e
        · exact .inr (Hp.subset (by simp only [List.mem_append, e, true_or, or_true]))
      · intro e
        rcases head_in_or_default 0 R with e' | e'
        · omega
        · exact nR (e ▸ e')
    | RLink block old =>
      obtain ⟨hb1, hb2, hb3⟩ := hS block (by simp [held])
      have hc := hcnt block
      simp only [held, List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hc
      have nL : block ∉ L := List.count_eq_zero.1 (by omega)
      have nR : block ∉ R := List.count_eq_zero.1 (by omega)
      have nD : block ∉ D := List.count_eq_zero.1 (by omega)
      have n1 : block ∉ held p1 := List.count_eq_zero.1 (by simp only [held]; omega)
      obtain ⟨v, hv⟩ := ai_backing_present base capacity h block Hback
        (by simp only [page_size]; omega)
      obtain ⟨Hold, Hne⟩ := Hc0
      apply ai_turn_intro
      simp only [turn, hv, Bool.false_eq_true, ↓reduceIte]
      refine ⟨L, R, D, ⟨Hbase, by ai_backing, m0, m1, by ai_look, by ai_look, by ai_look,
        linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
        linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR,
        linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CD, by ai_look, by ai_look,
        Hp, Hop, Ho, ⟨Hold, Hne, upd_eq _ _ _⟩,
        ai_cached_remote_frame _ _ _ _ _ Hc1 (fun c hc => by ai_frame hS c hc)⟩,
        ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
    | RCAS block old =>
      obtain ⟨hb1, hb2, hb3⟩ := hS block (by simp [held])
      have hc := hcnt block
      simp only [held, List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hc
      have n1 : block ∉ held p1 := List.count_eq_zero.1 (by simp only [held]; omega)
      obtain ⟨Hold, Hne, Hblk⟩ := Hc0
      apply ai_turn_intro
      by_cases he : R.headD 0 = old
      · subst he
        simp only [turn, Hr, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
        refine ⟨L, block :: R, D, ⟨Hbase, by ai_backing, m0, m1, by ai_look, by ai_look,
          by ai_look, linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
          ⟨by ai_look, linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR⟩,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CD, by ai_look, by ai_look,
          ai_perm_of_count (fun x => by
            simp only [List.count_append, List.count_cons, List.count_nil, held]; omega) Hp,
          Hop, Ho, trivial,
          ai_cached_remote_frame _ _ _ _ _ Hc1 (fun c hc => by ai_frame hS c hc)⟩,
          ownership_publish _ _ _ _ _ _ _ _ nofun⟩
      · have he' : (R.headD 0 == old) = false := beq_eq_false_iff_ne.2 he
        simp only [turn, Hr, he', Bool.false_eq_true, ↓reduceIte]
        exact ⟨L, R, D, ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, CD, Hm0, Hm1, Hp, Hop, Ho,
          trivial, Hc1⟩, ownership_remote _ _ _ _ _ _ nofun (.inr ⟨block, count, rfl⟩)⟩
  | Remote1 =>
    cases p1 with
    | RPoll =>
      by_cases hm : m1 = 0
      · subst hm
        apply ai_turn_intro
        simp only [turn, Hm1, beq_self_eq_true, ↓reduceIte]
        exact ⟨L, R, D, ⟨Hbase, Hback, m0, 0, Hr, Hl, Hd, CL, CR, CD, Hm0, Hm1, Hp, Hop, Ho, Hc0,
          Hc1⟩, ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
      · have hm' : (m1 == 0) = false := beq_eq_false_iff_ne.2 hm
        obtain ⟨hb1, hb2, hb3⟩ := hS m1 (by simp [mailbox_nodes, hm'])
        obtain ⟨v, hv⟩ := ai_backing_present base capacity h (m1 + 1) Hback
          (by simp only [page_size]; omega)
        apply ai_turn_intro
        simp (disch := ai_distinct) only [turn, Hm1, hm', Bool.false_eq_true, ↓reduceIte,
          upd_neq, hv]
        refine ⟨L, R, D, ⟨Hbase, by ai_backing, m0, 0, by ai_look, by ai_look, by ai_look,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CD, by ai_look, by ai_look,
          ai_perm_of_count (fun x => by
            simp only [List.count_append, mailbox_nodes, hm', beq_self_eq_true, ↓reduceIte,
              Bool.false_eq_true, held]; omega) Hp,
          Hop, Ho, ai_cached_remote_frame _ _ _ _ _ Hc0 (fun c hc => by ai_frame hS c hc),
          trivial⟩,
          ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
    | RRead block =>
      obtain ⟨hb1, hb2, hb3⟩ := hS block (by simp [held])
      have hc := hcnt block
      simp only [held, List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hc
      have nR : block ∉ R := List.count_eq_zero.1 (by omega)
      apply ai_turn_intro
      simp only [turn, Hr]
      refine ⟨L, R, D, ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, CD, Hm0, Hm1, Hp, Hop, Ho, Hc0,
        ⟨?_, ?_⟩⟩, ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
      · rcases head_in_or_default 0 R with e | e
        · exact .inl e
        · exact .inr (Hp.subset (by simp only [List.mem_append, e, true_or, or_true]))
      · intro e
        rcases head_in_or_default 0 R with e' | e'
        · omega
        · exact nR (e ▸ e')
    | RLink block old =>
      obtain ⟨hb1, hb2, hb3⟩ := hS block (by simp [held])
      have hc := hcnt block
      simp only [held, List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hc
      have nL : block ∉ L := List.count_eq_zero.1 (by omega)
      have nR : block ∉ R := List.count_eq_zero.1 (by omega)
      have nD : block ∉ D := List.count_eq_zero.1 (by omega)
      have n0 : block ∉ held p0 := List.count_eq_zero.1 (by simp only [held]; omega)
      obtain ⟨v, hv⟩ := ai_backing_present base capacity h block Hback
        (by simp only [page_size]; omega)
      obtain ⟨Hold, Hne⟩ := Hc1
      apply ai_turn_intro
      simp only [turn, hv, ↓reduceIte]
      refine ⟨L, R, D, ⟨Hbase, by ai_backing, m0, m1, by ai_look, by ai_look, by ai_look,
        linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
        linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR,
        linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CD, by ai_look, by ai_look,
        Hp, Hop, Ho, ai_cached_remote_frame _ _ _ _ _ Hc0 (fun c hc => by ai_frame hS c hc),
        ⟨Hold, Hne, upd_eq _ _ _⟩⟩,
        ownership_remote _ _ _ _ _ _ nofun (.inl rfl)⟩
    | RCAS block old =>
      obtain ⟨hb1, hb2, hb3⟩ := hS block (by simp [held])
      have hc := hcnt block
      simp only [held, List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hc
      have n0 : block ∉ held p0 := List.count_eq_zero.1 (by simp only [held]; omega)
      obtain ⟨Hold, Hne, Hblk⟩ := Hc1
      apply ai_turn_intro
      by_cases he : R.headD 0 = old
      · subst he
        simp only [turn, Hr, beq_self_eq_true, ↓reduceIte]
        refine ⟨L, block :: R, D, ⟨Hbase, by ai_backing, m0, m1, by ai_look, by ai_look,
          by ai_look, linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CL,
          ⟨by ai_look, linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CR⟩,
          linked_heap_frame _ _ _ _ (fun a ha => by ai_frame hS a ha) CD, by ai_look, by ai_look,
          ai_perm_of_count (fun x => by
            simp only [List.count_append, List.count_cons, List.count_nil, held]; omega) Hp,
          Hop, Ho, ai_cached_remote_frame _ _ _ _ _ Hc0 (fun c hc => by ai_frame hS c hc),
          trivial⟩,
          ownership_publish _ _ _ _ _ _ _ _ nofun⟩
      · have he' : (R.headD 0 == old) = false := beq_eq_false_iff_ne.2 he
        simp only [turn, Hr, he', Bool.false_eq_true, ↓reduceIte]
        exact ⟨L, R, D, ⟨Hbase, Hback, m0, m1, Hr, Hl, Hd, CL, CR, CD, Hm0, Hm1, Hp, Hop, Ho,
          Hc0, trivial⟩, ownership_remote _ _ _ _ _ _ nofun (.inr ⟨block, count, rfl⟩)⟩

theorem turn_view_step (base capacity : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) (L R D : List Nat) :
    allocator_view base capacity s L R D → turn base who s = some (t, event) →
    ∃ L' R' D', allocator_view base capacity t L' R' D' ∧
      ownership_transition who s.owner_state t.owner_state event L R D L' R' D' := by
  intro hview hturn
  obtain ⟨t', event', L', R', D', hturn', hview', hstep⟩ :=
    turn_view_complete base capacity who s L R D hview
  rw [hturn] at hturn'
  cases hturn'
  exact ⟨L', R', D', hview', hstep⟩

theorem turn_total (base capacity : Nat) (who : Actor) (s : AState) :
    allocator_inv base capacity s → ∃ t event, turn base who s = some (t, event) :=
  fun ⟨L, R, D, hview⟩ =>
    let ⟨t, event, _, _, _, hturn, _⟩ := turn_view_complete base capacity who s L R D hview
    ⟨t, event, hturn⟩

theorem turn_preserves_inv (base capacity : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) :
    allocator_inv base capacity s → turn base who s = some (t, event) →
    allocator_inv base capacity t := fun ⟨L, R, D, hview⟩ hturn =>
  let ⟨L', R', D', hview', _⟩ := turn_view_step base capacity who s t event L R D hview hturn
  ⟨L', R', D', hview'⟩

theorem allocator_initial_inv (capacity c : Nat) (s : AState) :
    s = initial_state capacity c → allocator_inv 1 capacity s := by
  rintro rfl; exact initial_state_inv capacity c

/-! ## The allocator's validity and construction interface

Exactly two instantiations of `Logic.Utils.Execution`; no example-local execution record,
constructor or replay proof remains. -/

def allocator_valid (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) : Prop :=
  execution_valid (fun who s o s' => turn 1 who s = some (s', o))
    (fun s => s = initial_state capacity c) e

def allocator_execution (capacity c : Nat) (picks : Nat → Actor) :
    Execution AState Actor (List (CSLObs (Nat × Nat))) :=
  execution_of_choices (turn 1) (allocator_inv 1 capacity)
    (fun who s hs => let ⟨t, ev, h⟩ := turn_total 1 capacity who s hs; ⟨(t, ev), h⟩)
    (turn_preserves_inv 1 capacity) (initial_state capacity c) (initial_state_inv capacity c) picks

-- Not ported: the Rocq `Ltac`s `ai_member`, `ai_block_bounds`, `ai_count_contradiction`,
-- `ai_permutation`, `ai_cached`, `ai_obligation`, `ai_finish` (replaced by the lemmas
-- `ai_block_bounds`, `ai_nodup_count`, `ai_perm_of_count`, `ai_ne_of_mem`, `ai_turn_intro`,
-- `linked_heap_frame` and the macros `ai_distinct`, `ai_heap`, `ai_interval`, `ai_backing`,
-- `ai_look`, `ai_frame`).

end Examples.CSL.Allocator.Model
