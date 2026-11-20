/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Representation

/-!
# Concrete queue heaps and the contiguous runtime layout

A generic heap `qheap hdr ns vs` satisfying the exact representation, and the runtime-base layout
that places the header at `hdr` and the nodes contiguously after it, with the heap builders
`fill_nodes_heap`, `init_queue_heap`, `new_queue_heap` (← `examples/CSL/Queue/Layout.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Layout
open Tisl Tisl.Heap Examples.CSL.Queue.Representation

/-! ## A generic queue heap -/

/-- The node cells of `ns` holding the payloads `vs` and the null-terminated links. -/
def nodeval (ns vs : List Nat) : Heap := apply_writes (node_writes ns vs).reverse hemp

def qheap (hdr : Nat) (ns vs : List Nat) : Heap :=
  fun x => if x = hdr then some (ns.getLastD 0)
    else if x = hdr + 1 then some (ns.headD 0)
    else nodeval ns vs x

theorem nodeval_dom (ns vs : List Nat) (x : Nat) : nodeval ns vs x ≠ none → x ∈ cells ns := by
  intro h
  rcases (apply_writes_dom_exact _ _ _).1 h with h | h
  · rw [List.map_reverse, List.mem_reverse] at h
    exact node_writes_keys_subset _ _ _ h
  · exact absurd rfl h

theorem nodeval_in (ns vs : List Nat) (x : Nat) :
    ns.length = vs.length → x ∈ cells ns → nodeval ns vs x ≠ none :=
  fun hlen hx => (node_writes_dom ns vs x hlen).2 hx

theorem nodeval_chain (hdr : Nat) (ns vs : List Nat) :
    qwf hdr ns → ns.length = vs.length → chain (nodeval ns vs) ns vs 0 := by
  intro hwf hlen
  cases ns with
  | nil => cases vs with
    | nil => exact chain_nil _ _
    | cons _ _ => simp at hlen
  | cons a ns =>
    have hnd : (cells (a :: ns)).Nodup := cells_nodup _ (List.nodup_cons.1 hwf.1).2
      fun b d hb hd => hwf.2.2 b d (.tail _ hb) (.tail _ hd)
    have hnext : vs.length = ((a :: ns).tail ++ [0]).length := by simp at hlen ⊢; omega
    have hcontents := node_writes_contents (a :: ns) vs hlen hnd
    have hpayload := Forall2_map_right (fun b v => nodeval (a :: ns) vs b = some v) Prod.fst _ _
      (Forall2_impl' _ _ _ _ hcontents fun _ _ _ _ hp => hp.1)
    have hlinks := Forall2_map_right (fun b nx => nodeval (a :: ns) vs (b + 1) = some nx)
      Prod.snd _ _ (Forall2_impl' _ _ _ _ hcontents fun _ _ _ _ hp => hp.2)
    rw [map_fst_combine _ _ hnext] at hpayload
    rw [map_snd_combine _ _ hnext] at hlinks
    exact ⟨linked_of_Forall2 _ _ _ hlinks, hpayload⟩

theorem qheap_qrep (hdr : Nat) (ns vs : List Nat) :
    qwf hdr ns → ns.length = vs.length → ns ≠ [] → qrep hdr ns vs (qheap hdr ns vs) := by
  intro hwf hlen hne
  have hhnc := qwf_hdr_cells _ _ hwf
  have hshnc := qwf_shdr_cells _ _ hwf
  have hhdr : qheap hdr ns vs hdr = some (ns.getLastD 0) := by simp [qheap]
  have hshdr : qheap hdr ns vs (hdr + 1) = some (ns.headD 0) := by simp [qheap]
  have hcell : ∀ x, x ∈ cells ns → qheap hdr ns vs x = nodeval ns vs x := by
    intro x hx
    have h1 : x ≠ hdr := by rintro rfl; exact hhnc hx
    have h2 : x ≠ hdr + 1 := by rintro rfl; exact hshnc hx
    simp [qheap, h1, h2]
  refine ⟨hwf, hshdr, ?_, chain_mono _ _ _ _ _ (nodeval_chain hdr ns vs hwf hlen) hcell, ?_, ?_⟩
  · cases ns with
    | nil => exact absurd rfl hne
    | cons _ _ => exact hhdr
  · have h0 : (0 : Nat) ≠ hdr := fun e => qwf_zero _ _ hwf (e ▸ .head _)
    simp only [qheap, h0, ↓reduceIte, Nat.zero_ne_add_one]
    rcases e : nodeval ns vs 0 with _ | w
    · rfl
    · exact absurd (.tail _ (.tail _ (nodeval_dom ns vs 0 (by rw [e]; simp))))
        (qwf_zero _ _ hwf)
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hhdr]; simp
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hshdr]; simp
    · rw [hcell x hx]; exact nodeval_in _ _ _ hlen hx

theorem qheap_qex (hdr : Nat) (ns vs : List Nat) : qex hdr ns (qheap hdr ns vs) := by
  intro x hx
  simp only [qheap] at hx
  split at hx
  · subst_vars; exact .head _
  split at hx
  · subst_vars; exact .tail _ (.head _)
  · exact .tail _ (.tail _ (nodeval_dom _ _ _ hx))

/-! ## Runtime-base contiguous queue layout -/

def queue_nodes (hdr count : Nat) : List Nat := node_addrs (hdr + 2) count

def fill_nodes_heap (first : Nat) (values : List Nat) (h : Heap) : Heap :=
  apply_writes (node_writes (node_addrs first values.length) values) h

def init_queue_heap (hdr : Nat) (values : List Nat) (h : Heap) : Heap :=
  let ns := queue_nodes hdr values.length
  fill_nodes_heap (hdr + 2) values (upd (upd h hdr (ns.getLastD 0)) (hdr + 1) (ns.headD 0))

def new_queue_heap (hdr : Nat) (values : List Nat) (h : Heap) : Heap :=
  init_queue_heap hdr values (hunion (hblock hdr (2 * (values.length + 1))) h)

theorem queue_nodes_length (hdr count : Nat) : (queue_nodes hdr count).length = count :=
  node_addrs_length _ _

theorem queue_nodes_qwf (hdr count : Nat) : 0 < hdr → qwf hdr (queue_nodes hdr count) := by
  intro hhdr
  show (node_addrs hdr (count + 1)).Nodup ∧ 0 ∉ node_addrs hdr (count + 1) ∧
    ∀ a b, a ∈ node_addrs hdr (count + 1) → b ∈ node_addrs hdr (count + 1) → a ≠ b + 1
  refine ⟨node_addrs_nodup _ _, fun hin => ?_, fun a b ha hb => ?_⟩
  · obtain ⟨j, -, hx⟩ := (node_addrs_in _ _ _).1 hin; omega
  · obtain ⟨j, -, rfl⟩ := (node_addrs_in _ _ _).1 ha
    obtain ⟨k, -, rfl⟩ := (node_addrs_in _ _ _).1 hb
    omega

theorem queue_cells_range (hdr count x : Nat) :
    x ∈ qcells hdr (queue_nodes hdr count) ↔ hdr ≤ x ∧ x < hdr + 2 * (count + 1) :=
  node_cells_range hdr (count + 1) x

theorem qheap_queue_nodes_rep (hdr : Nat) (values : List Nat) :
    0 < hdr →
      qrep hdr (queue_nodes hdr values.length) values
        (qheap hdr (queue_nodes hdr values.length) values) := by
  intro hhdr
  cases values with
  | nil =>
    show qrep hdr [] [] (qheap hdr [] [])
    have htail : qheap hdr [] [] hdr = some 0 := by simp [qheap]
    have hhead : qheap hdr [] [] (hdr + 1) = some 0 := by simp [qheap]
    refine ⟨queue_nodes_qwf hdr 0 hhdr, hhead, by show qheap hdr [] [] hdr ≠ none; simp [htail],
      chain_nil _ _, ?_, ?_⟩
    · have h0 : (0 : Nat) ≠ hdr := by omega
      simp only [qheap, h0, ↓reduceIte, Nat.zero_ne_add_one]; rfl
    · intro x hx
      simp only [qcells, cells, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl
      · simp [htail]
      · simp [hhead]
  | cons value values =>
    exact qheap_qrep _ _ _ (queue_nodes_qwf _ _ hhdr) (queue_nodes_length _ _) (by
      simp [queue_nodes, node_addrs])

theorem nodeval_node_addrs_out (first : Nat) (values : List Nat) (x : Nat) :
    (x < first ∨ first + 2 * values.length ≤ x) →
      nodeval (node_addrs first values.length) values x = none := by
  intro hout
  rcases e : nodeval (node_addrs first values.length) values x with _ | w
  · rfl
  · have := (node_cells_range _ _ _).1 (nodeval_dom _ _ x (by rw [e]; simp))
    omega

/-- Filling a strided list changes exactly its node cells. -/
theorem fill_nodes_heap_lookup (first : Nat) (values : List Nat) (h : Heap) (x : Nat) :
    fill_nodes_heap first values h x =
      match nodeval (node_addrs first values.length) values x with
      | some value => some value
      | none => h x := by
  unfold fill_nodes_heap nodeval
  rw [← apply_writes_rev _ h (node_writes_nodup _ _ (node_addrs_length _ _)
    (node_addrs_cells_nodup _ _)) x, apply_writes_lookup, apply_writes_lookup]
  split <;> simp_all [hemp]

theorem init_queue_heap_agrees (hdr : Nat) (values : List Nat) (h : Heap) :
    heq (init_queue_heap hdr values h)
      (hunion (qheap hdr (queue_nodes hdr values.length) values) h) := by
  intro x
  dsimp only [init_queue_heap]
  rw [fill_nodes_heap_lookup]
  simp only [hunion, qheap, queue_nodes]
  by_cases hx : x = hdr
  · subst hx
    rw [nodeval_node_addrs_out _ _ _ (.inl (by omega)), upd_neq _ _ _ _ (by omega), upd_eq]
    simp
  · by_cases hsx : x = hdr + 1
    · subst hsx
      rw [nodeval_node_addrs_out _ _ _ (.inl (by omega)), upd_eq]
      simp
    · rw [upd_neq _ _ _ _ hsx, upd_neq _ _ _ _ hx]
      simp only [hx, hsx, ↓reduceIte]; rfl

theorem new_queue_heap_agrees (hdr : Nat) (values : List Nat) (h : Heap) :
    0 < hdr → block_free h hdr (2 * (values.length + 1)) →
      heq (new_queue_heap hdr values h)
        (hunion (qheap hdr (queue_nodes hdr values.length) values) h) := by
  intro hhdr _ x
  unfold new_queue_heap
  rw [init_queue_heap_agrees hdr values _ x]
  simp only [hunion]
  split
  · rfl
  · rename_i e
    have hout : hblock hdr (2 * (values.length + 1)) x = none := by
      refine hblock_out _ _ _ ?_
      refine (Nat.lt_or_ge x hdr).imp_right fun hlo => ?_
      refine Nat.le_of_not_lt fun hhi => ?_
      exact qrep_fp _ _ _ _ (qheap_queue_nodes_rep hdr values hhdr) x
        ((queue_cells_range _ _ _).2 ⟨hlo, hhi⟩) e
    rw [hout]

theorem new_queue_heap_disjoint (hdr : Nat) (values : List Nat) (h : Heap) :
    block_free h hdr (2 * (values.length + 1)) →
      hdisj (qheap hdr (queue_nodes hdr values.length) values) h := by
  intro hfree x
  rcases e : qheap hdr (queue_nodes hdr values.length) values x with _ | w
  · exact .inl rfl
  · refine .inr ?_
    have hin := qheap_qex hdr (queue_nodes hdr values.length) values x (by rw [e]; simp)
    obtain ⟨hlo, hhi⟩ := (queue_cells_range _ _ _).1 hin
    have := hfree (x - hdr) (by omega)
    rwa [Nat.add_sub_cancel' hlo] at this

theorem fill_nodes_heap_finite (first : Nat) (values : List Nat) (h : Heap) :
    heap_finite h → heap_finite (fill_nodes_heap first values h) :=
  apply_writes_finite _ _

theorem new_queue_heap_finite (hdr : Nat) (values : List Nat) (h : Heap) :
    heap_finite h → heap_finite (new_queue_heap hdr values h) := fun hh =>
  fill_nodes_heap_finite _ _ _ (heap_finite_upd _ _ _ (heap_finite_upd _ _ _
    (heap_finite_hunion _ _ (heap_finite_hblock _ _) hh)))

end Examples.CSL.Queue.Layout
