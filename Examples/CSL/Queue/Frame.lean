/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Recurrence
public import Examples.CSL.Queue.Trace
public import Examples.CSL.Queue.Layout

/-!
# Separation and framing of heap-backed queue recurrence

The precise representation `qrepX = qrep ∧ qex` and the transport theorem `qrepX_frame` (a heap
that is the queue, disjointly extended by a null-avoiding frame, contains the queue); the converse
`qrep_decompose` with uniqueness `qrep_decompose_unique`; transport corollaries of the recurrence
theorems; and frame preservation `qstepN_agree`/`frame_assertion_preserved`
(← `examples/CSL/Queue/Frame.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Frame
open Tisl Tisl.Heap Tisl.Pcm Tisl.Ctx Tisl.CSL Tisl.Notation
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Layout Examples.CSL.Queue.Trace
open Examples.CSL.Queue.Sequential Examples.CSL.Queue.Recurrence

/-! ## The precise representation predicate -/

def qrepX (hdr : Nat) (ns vs : List Nat) (h : Heap) : Prop := qrep hdr ns vs h ∧ qex hdr ns h

theorem qrepX_qrep (hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrepX hdr ns vs h → qrep hdr ns vs h := And.left

/-- `qrep` looks only at the footprint and the null cell, so it survives any change leaving both
alone. -/
theorem qrep_agree_fp (hdr : Nat) (ns vs : List Nat) (h h' : Heap) :
    qrep hdr ns vs h → (∀ x, x ∈ qcells hdr ns → h' x = h x) → h' 0 = none →
      qrep hdr ns vs h' := by
  rintro ⟨hwf, hhd, htl, hch, -, hfp⟩ hag h0
  refine ⟨hwf, ?_, ?_, chain_mono _ _ _ _ _ hch fun x hx => hag x (.tail _ (.tail _ hx)),
    h0, fun x hx => (hag x hx).symm ▸ hfp x hx⟩
  · rw [hag _ (.tail _ (.head _))]; exact hhd
  · unfold tailok at htl ⊢
    cases ns <;> (rw [hag _ (.head _)]; exact htl)

/-- The transport theorem on the precondition: the frame owns no queue cell and does not allocate
the null address (both refuted by counterexample in `Overlap`). -/
theorem qrepX_frame (hdr : Nat) (ns vs : List Nat) (h f : Heap) :
    qrepX hdr ns vs h → hdisj h f → f 0 = none → qrep hdr ns vs (hunion h f) := by
  rintro ⟨hq, -⟩ - hf0
  exact qrep_agree_fp _ _ _ _ _ hq (fun x hx => hunion_eq _ _ _ (qrep_fp _ _ _ _ hq x hx))
    (hunion_null _ _ (qrep_null _ _ _ _ hq) hf0)

/-- A precise queue owns nothing outside its footprint. -/
theorem qex_out (hdr : Nat) (ns : List Nat) (h : Heap) (x : Nat) :
    qex hdr ns h → x ∉ qcells hdr ns → h x = none := fun hex hout =>
  Classical.byContradiction fun hx => hout (hex x hx)

/-! ## The canonical decomposition, and its uniqueness -/

def inqb (hdr : Nat) (ns : List Nat) (x : Nat) : Bool := decide (x ∈ qcells hdr ns)

theorem inqb_true (hdr : Nat) (ns : List Nat) (x : Nat) :
    inqb hdr ns x = true ↔ x ∈ qcells hdr ns := by simp [inqb]

theorem inqb_false (hdr : Nat) (ns : List Nat) (x : Nat) :
    inqb hdr ns x = false ↔ x ∉ qcells hdr ns := by simp [inqb]

def qloc (hdr : Nat) (ns : List Nat) (H : Heap) : Heap :=
  fun x => if inqb hdr ns x then H x else none

def qfrm (hdr : Nat) (ns : List Nat) (H : Heap) : Heap :=
  fun x => if inqb hdr ns x then none else H x

theorem qloc_in (hdr : Nat) (ns : List Nat) (H : Heap) (x : Nat) :
    x ∈ qcells hdr ns → qloc hdr ns H x = H x := fun hx => by
  simp [qloc, (inqb_true _ _ _).2 hx]

theorem qloc_out (hdr : Nat) (ns : List Nat) (H : Heap) (x : Nat) :
    x ∉ qcells hdr ns → qloc hdr ns H x = none := fun hx => by
  simp [qloc, (inqb_false _ _ _).2 hx]

theorem qfrm_in (hdr : Nat) (ns : List Nat) (H : Heap) (x : Nat) :
    x ∈ qcells hdr ns → qfrm hdr ns H x = none := fun hx => by
  simp [qfrm, (inqb_true _ _ _).2 hx]

theorem qfrm_out (hdr : Nat) (ns : List Nat) (H : Heap) (x : Nat) :
    x ∉ qcells hdr ns → qfrm hdr ns H x = H x := fun hx => by
  simp [qfrm, (inqb_false _ _ _).2 hx]

theorem qrep_decompose (hdr : Nat) (ns vs : List Nat) (H : Heap) :
    qrep hdr ns vs H →
      qrepX hdr ns vs (qloc hdr ns H) ∧ hdisj (qloc hdr ns H) (qfrm hdr ns H) ∧
        heq H (hunion (qloc hdr ns H) (qfrm hdr ns H)) ∧ qfrm hdr ns H 0 = none := by
  intro hq
  have hnull := qrep_null _ _ _ _ hq
  refine ⟨⟨qrep_agree_fp _ _ _ _ _ hq (fun x hx => qloc_in _ _ _ _ hx) ?_, ?_⟩, ?_, ?_, ?_⟩
  · by_cases h0 : 0 ∈ qcells hdr ns
    · rw [qloc_in _ _ _ _ h0]; exact hnull
    · exact qloc_out _ _ _ _ h0
  · intro x hx
    by_cases hin : x ∈ qcells hdr ns
    · exact hin
    · exact absurd (qloc_out _ _ _ _ hin) hx
  · intro x; unfold qloc qfrm; cases inqb hdr ns x <;> simp
  · intro x; unfold hunion qloc qfrm; cases inqb hdr ns x <;> simp
    cases H x <;> rfl
  · by_cases h0 : 0 ∈ qcells hdr ns
    · exact qfrm_in _ _ _ _ h0
    · rw [qfrm_out _ _ _ _ h0]; exact hnull

/-- Precision: the split is unique, so "the frame" is a function of the state. -/
theorem qrep_decompose_unique (hdr : Nat) (ns vs : List Nat) (H h f : Heap) :
    qrepX hdr ns vs h → hdisj h f → heq H (hunion h f) →
      heq h (qloc hdr ns H) ∧ heq f (qfrm hdr ns H) := by
  rintro ⟨hq, hex⟩ hdj heqh
  have hfp := qrep_fp _ _ _ _ hq
  refine ⟨fun x => ?_, fun x => ?_⟩ <;> by_cases hin : x ∈ qcells hdr ns
  · rw [qloc_in _ _ _ _ hin, heqh, hunion_eq _ _ _ (hfp x hin)]
  · rw [qloc_out _ _ _ _ hin]; exact qex_out _ _ _ _ hex hin
  · rw [qfrm_in _ _ _ _ hin]
    exact (hdj x).resolve_left (hfp x hin)
  · rw [qfrm_out _ _ _ _ hin, heqh, hunion_none _ _ _ (qex_out _ _ _ _ hex hin)]

/-! ## The transport corollaries

`Recurrence` applied to framed representation premises; its composition of structural AG/AU rules
is reused unchanged. -/

theorem rotate_agaf_pop_framed (hdr nlv : Nat) (ns vs : List Nat) (d : Nat) (h f allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    qrepX hdr ns vs h → hdisj h f → f 0 = none → find_index Nat.beq nlv vs = some d →
      entails (AG (AF (visWₜ (csl_indexed fun o : Indexed Nat => o.value = nlv))))
        (run hdr ((hunion h f, allocs), (ctx, c))) .pure := fun hx hd hf hfind =>
  rotate_agaf_pop_heap hdr nlv _ allocs ctx c ns vs d (qrepX_frame _ _ _ _ _ hx hd hf) hfind

theorem rotate_agaf_pop_fresh_framed (hdr nlv : Nat) (ns vs : List Nat) (d : Nat)
    (h f allocs : Heap) (ctx : Ctx) (c k : Nat) :
    qrepX hdr ns vs h → hdisj h f → f 0 = none → find_index Nat.beq nlv vs = some d →
      entails (AG (AF (visWₜ (csl_indexed (indexed_after (fun x => x = nlv) k)))))
        (run hdr ((hunion h f, allocs), (ctx, c))) .pure := fun hx hd hf hfind =>
  rotate_agaf_pop_fresh hdr nlv _ allocs ctx c ns vs d k (qrepX_frame _ _ _ _ _ hx hd hf) hfind

/-- An element absent from the owned queue is never observed, whatever the frame stores. -/
theorem absent_never_observed_framed (hdr : Nat) (ns vs : List Nat) (nlv : Nat)
    (h f allocs : Heap) (ctx : Ctx) (c : Nat) :
    qrepX hdr ns vs h → hdisj h f → f 0 = none → ns ≠ [] → nlv ∉ vs →
      entails (AG (.now (obs_sat fun x => x ≠ nlv)))
        (run hdr ((hunion h f, allocs), (ctx, c))) .pure := fun hx hd hf hne hnin =>
  absent_never_observed hdr _ allocs ctx c ns vs nlv (qrepX_frame _ _ _ _ _ hx hd hf) hne hnin

/-- An empty owned queue is stuck even beside a large populated frame. -/
theorem empty_queue_no_ag_framed (hdr : Nat) (vs : List Nat) (h f allocs : Heap) (ctx : Ctx)
    (c : Nat) (w : World (writerE (CSLObs Nat))) (φ : TiclL (writerE (CSLObs Nat))) :
    qrepX hdr [] vs h → hdisj h f → f 0 = none →
      ¬ entails (AG φ) (run hdr ((hunion h f, allocs), (ctx, c))) w := fun hx hd hf =>
  empty_queue_no_ag hdr _ allocs ctx c vs w φ (qrepX_frame _ _ _ _ _ hx hd hf)

/-! ## Frame preservation -/

theorem qcells_writes (hdr a : Nat) (ns : List Nat) :
    hdr ∈ qcells hdr (a :: ns) ∧ hdr + 1 ∈ qcells hdr (a :: ns) ∧
      a + 1 ∈ qcells hdr (a :: ns) ∧ zof hdr ns + 1 ∈ qcells hdr (a :: ns) := by
  refine ⟨.head _, .tail _ (.head _), .tail _ (.tail _ ((in_cells _ _).2 ⟨a, .head _, .inr rfl⟩)),
    ?_⟩
  cases ns with
  | nil => exact .tail _ (.head _)
  | cons b ns' =>
    refine .tail _ (.tail _ ((in_cells _ _).2 ⟨zof hdr (b :: ns'), ?_, .inr rfl⟩))
    exact .tail _ (last_in (b :: ns') 0 (by simp))

theorem qstep_agree (hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → ns ≠ [] → agree_out (qcells hdr ns) h (qstep hdr ns h) := by
  intro _ hne
  match ns, hne with
  | a :: ns', _ =>
    obtain ⟨h1, h2, h3, h4⟩ := qcells_writes hdr a ns'
    intro x hx
    exact rot_heap_other _ _ _ _ _ _ (by rintro rfl; exact hx h1) (by rintro rfl; exact hx h3)
      (by rintro rfl; exact hx h4) (by rintro rfl; exact hx h2)

theorem qcells_rotl (hdr : Nat) (ns : List Nat) (x : Nat) :
    ns ≠ [] → (x ∈ qcells hdr (rotl ns) ↔ x ∈ qcells hdr ns) := by
  intro hne
  match ns, hne with
  | a :: ns', _ => exact qcells_rot hdr a ns' x

theorem qstepN_agree (n hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → ns ≠ [] → agree_out (qcells hdr ns) h (qstepN hdr n ns h) := by
  intro hq hne
  have key : ∀ n, (∀ x, x ∈ qcells hdr (rotlN n ns) ↔ x ∈ qcells hdr ns) ∧
      agree_out (qcells hdr ns) h (qstepN hdr n ns h) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => .rfl, fun _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨hqn, hnen⟩ := qstepN_qrep n hdr ns vs h hq hne
      refine ⟨fun x => (qcells_rotl _ _ x hnen).trans (ih.1 x), fun x hx => ?_⟩
      rw [qstepN_succ, qstep_agree _ _ _ _ hqn hnen x fun hin => hx ((ih.1 x).1 hin)]
      exact ih.2 x hx
  exact (key n).2

/-- The frame sub-heap is preserved pointwise, for every number of rotations. -/
theorem frame_preserved (n hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → ns ≠ [] → heq (qfrm hdr ns h) (qfrm hdr ns (qstepN hdr n ns h)) := by
  intro hq hne x
  by_cases hin : x ∈ qcells hdr ns
  · rw [qfrm_in _ _ _ _ hin, qfrm_in _ _ _ _ hin]
  · rw [qfrm_out _ _ _ _ hin, qfrm_out _ _ _ _ hin, qstepN_agree n hdr ns vs h hq hne x hin]

theorem frame_assertion_preserved (A : Heap → Prop) (n hdr : Nat) (ns vs : List Nat) (h : Heap) :
    (∀ h1 h2, heq h1 h2 → A h1 → A h2) → qrep hdr ns vs h → ns ≠ [] →
      A (qfrm hdr ns h) → A (qfrm hdr ns (qstepN hdr n ns h)) := fun hA hq hne hAf =>
  hA _ _ (frame_preserved n hdr ns vs h hq hne) hAf

/-- The version on the original frame `f` of a separating decomposition. -/
theorem frame_assertion_preserved_sep (A : Heap → Prop) (n hdr : Nat) (ns vs : List Nat)
    (h f : Heap) :
    (∀ h1 h2, heq h1 h2 → A h1 → A h2) → qrepX hdr ns vs h → hdisj h f → f 0 = none →
      ns ≠ [] → A f → A (qfrm hdr ns (qstepN hdr n ns (hunion h f))) := by
  intro hA hx hd hf hne hAf
  have hqH := qrepX_frame _ _ _ _ _ hx hd hf
  have hfeq := (qrep_decompose_unique hdr ns vs (hunion h f) h f hx hd fun _ => rfl).2
  exact frame_assertion_preserved A n hdr ns vs _ hA hqH hne (hA _ _ hfeq hAf)

/-- A newly initialized queue owns its block beside the unchanged old heap. -/
theorem new_queue_heap_owned (hdr : Nat) (values : List Nat) (h : Heap) :
    0 < hdr → block_free h hdr (2 * (values.length + 1)) →
      asep (qrepX hdr (queue_nodes hdr values.length) values) (fun frame => heq frame h)
        (new_queue_heap hdr values h) :=
  fun hhdr hfree => ⟨qheap hdr (queue_nodes hdr values.length) values, h,
    new_queue_heap_disjoint _ _ _ hfree, new_queue_heap_agrees _ _ _ hhdr hfree,
    ⟨qheap_queue_nodes_rep _ _ hhdr, qheap_qex _ _ _⟩, fun _ => rfl⟩

end Examples.CSL.Queue.Frame
