/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.HeapModel

/-!
# A finite link-first allocator page

The five metadata cells precede stride-two blocks. A block's first cell is its free-list link;
its successor cell is mutable client payload. The stride-two geometry (`cells`, `node_addrs`,
`init_links_heap`) is owned by `Logic.Sep.HeapModel`; this module only fixes the page layout
(← `examples/CSL/Allocator/Layout.v`).
-/

@[expose] public section
namespace Examples.CSL.Allocator.Layout
open Tisl.Heap

def page_size (capacity : Nat) : Nat := 5 + 2 * capacity
def remote_head (base : Nat) : Nat := base
def local_head (base : Nat) : Nat := base + 1
def drain_head (base : Nat) : Nat := base + 2
def mailbox (base : Nat) (client : Bool) : Nat :=
  base + 3 + (if client then 1 else 0)
def page_blocks (base capacity : Nat) : List Nat :=
  node_addrs (base + 5) capacity
def tag_alloc : Nat := 0
def tag_retire : Nat := 1
def tag_reclaim : Nat := 2
def tag_retry : Nat := 3

theorem page_size_positive (capacity : Nat) : 0 < page_size capacity := by
  unfold page_size; omega

theorem page_blocks_in (base capacity b : Nat) :
    b ∈ page_blocks base capacity ↔ ∃ j, j < capacity ∧ b = base + 5 + 2 * j :=
  node_addrs_in _ _ _

theorem page_blocks_length (base capacity : Nat) :
    (page_blocks base capacity).length = capacity :=
  node_addrs_length _ _

theorem page_blocks_nodup (base capacity : Nat) : (page_blocks base capacity).Nodup :=
  node_addrs_nodup _ _

theorem page_blocks_bounds (base capacity b : Nat) :
    b ∈ page_blocks base capacity → base + 5 ≤ b ∧ b + 1 < base + page_size capacity := by
  intro hin
  obtain ⟨j, hj, rfl⟩ := (page_blocks_in _ _ _).1 hin
  unfold page_size; omega

theorem page_blocks_link_payload_disjoint (base capacity a b : Nat) :
    a ∈ page_blocks base capacity → b ∈ page_blocks base capacity → a ≠ b + 1 :=
  node_addrs_link_payload_disjoint _ _ _ _

/-! ## Pure counterparts of the checked initialization writes

The order here is the source order: remote, drain, mailbox 0, mailbox 1, local; then links from
low to high. The allocation overlay installs the zero payloads. Initialization never writes a
payload cell. -/

def page_heap (base capacity : Nat) (h : Heap) : Heap :=
  init_links_heap (base + 5) capacity
    (upd
      (upd
        (upd
          (upd
            (upd (hunion (hblock base (page_size capacity)) h)
              (remote_head base) 0)
            (drain_head base) 0)
          (mailbox base false) 0)
        (mailbox base true) 0)
      (local_head base) (match capacity with | 0 => 0 | _ + 1 => base + 5))

/-! ## Backing storage, checked cells, and the old frame -/

theorem page_backing_in (base capacity : Nat) (h : Heap) (x : Nat) :
    (base ≤ x ∧ x < base + page_size capacity) →
    hunion (hblock base (page_size capacity)) h x = some 0 := by
  rintro ⟨hlo, hhi⟩
  apply hunion_some
  have := hblock_in base (page_size capacity) (x - base) (by omega)
  rwa [Nat.add_sub_cancel' hlo] at this

theorem page_heap_frame (base capacity : Nat) (h : Heap) (x : Nat) :
    (x < base ∨ base + page_size capacity ≤ x) → page_heap base capacity h x = h x := by
  intro hout
  unfold page_size at hout
  unfold page_heap
  rw [init_links_heap_out _ _ _ _ (by omega)]
  rw [upd_neq, upd_neq, upd_neq, upd_neq, upd_neq,
    hunion_none _ _ _ (hblock_out _ _ _ (by unfold page_size; omega))]
  all_goals
    simp only [remote_head, local_head, drain_head, mailbox, Bool.false_eq_true, ↓reduceIte]
    omega

theorem page_heap_in (base capacity : Nat) (h : Heap) (x : Nat) :
    (base ≤ x ∧ x < base + page_size capacity) → page_heap base capacity h x ≠ none := by
  intro hin
  refine (init_links_heap_dom _ _ _ _).2 (Or.inr ?_)
  repeat apply upd_mono
  rw [page_backing_in _ _ _ _ hin]; simp

theorem page_heap_dom (base capacity : Nat) (h : Heap) (x : Nat) :
    page_heap base capacity h x ≠ none ↔
      (base ≤ x ∧ x < base + page_size capacity) ∨ h x ≠ none := by
  by_cases hin : base ≤ x ∧ x < base + page_size capacity
  · exact ⟨fun _ => Or.inl hin, fun _ => page_heap_in _ _ _ _ hin⟩
  · rw [page_heap_frame _ _ _ _ (by omega)]
    exact ⟨Or.inr, fun h' => h'.resolve_left hin⟩

theorem page_heap_closed_dom (base capacity x : Nat) :
    page_heap base capacity hemp x ≠ none ↔ base ≤ x ∧ x < base + page_size capacity := by
  rw [page_heap_dom]
  exact ⟨fun h => h.resolve_right fun h' => h' rfl, Or.inl⟩

theorem page_heap_old_frame (base capacity : Nat) (h : Heap) :
    block_free h base (page_size capacity) →
    ∀ x, h x ≠ none → page_heap base capacity h x = h x := by
  intro hfree x hx
  refine page_heap_frame _ _ _ _ (Classical.byContradiction fun hin => hx ?_)
  have := hfree (x - base) (by omega)
  rwa [Nat.add_sub_cancel' (by omega)] at this

theorem page_heap_finite (base capacity : Nat) (h : Heap) :
    heap_finite h → heap_finite (page_heap base capacity h) := by
  intro hh
  unfold page_heap
  apply init_links_heap_finite
  repeat apply heap_finite_upd
  exact heap_finite_hunion _ _ (heap_finite_hblock _ _) hh

/-! ## Initialized contents -/

theorem page_heap_remote (base capacity : Nat) (h : Heap) :
    page_heap base capacity h (remote_head base) = some 0 := by
  unfold page_heap
  rw [init_links_heap_out _ _ _ _ (by simp [remote_head])]
  simp [upd, remote_head, local_head, drain_head, mailbox]

theorem page_heap_drain (base capacity : Nat) (h : Heap) :
    page_heap base capacity h (drain_head base) = some 0 := by
  unfold page_heap
  rw [init_links_heap_out _ _ _ _ (by simp [drain_head])]
  simp [upd, local_head, drain_head, mailbox]

theorem page_heap_mailbox (base capacity : Nat) (h : Heap) (client : Bool) :
    page_heap base capacity h (mailbox base client) = some 0 := by
  unfold page_heap
  rw [init_links_heap_out _ _ _ _ (by cases client <;> simp [mailbox])]
  cases client <;> simp [upd, local_head, mailbox]

theorem page_heap_local (base capacity : Nat) (h : Heap) :
    page_heap base capacity h (local_head base) =
      some (match capacity with | 0 => 0 | _ + 1 => base + 5) := by
  unfold page_heap
  rw [init_links_heap_out _ _ _ _ (by simp [local_head])]
  exact upd_eq _ _ _

theorem page_heap_local_blocks (base capacity : Nat) (h : Heap) :
    page_heap base capacity h (local_head base) = some ((page_blocks base capacity).headD 0) := by
  rw [page_heap_local]; cases capacity <;> rfl

theorem page_heap_link (base capacity : Nat) (h : Heap) (pre : List Nat) (b : Nat)
    (rest : List Nat) :
    page_blocks base capacity = pre ++ b :: rest →
    page_heap base capacity h b = some (rest.headD 0) :=
  init_links_heap_link _ _ _ pre b rest

end Examples.CSL.Allocator.Layout
