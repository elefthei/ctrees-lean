/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Frame

/-!
# Overlap: the compatibility preconditions are load-bearing

`Frame.qrepX_frame` asks two things of a frame `f`: (C1) `hdisj h f`, the frame owns no queue
cell; (C2) `f 0 = none`, the frame does not allocate the null address. Each is refuted twice: the
check rejects the candidate frame, and the conclusion the frame rule would license is false. The
witness queue has header `2`, nodes `[4, 6]`, payloads `[7, 9]` (← `examples/CSL/Overlap.v`).
-/

@[expose] public section
namespace Examples.CSL.Overlap
open Tisl Tisl.Heap
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Layout Examples.CSL.Queue.Trace

/-- The witness queue heap (Rocq section `Let`; public because the statements mention it). -/
def h1 : Heap := qheap 2 [4, 6] [7, 9]
/-- The candidate frame claims address 3, the queue's head-pointer cell. -/
def fbad : Heap := hsingle 3 42
/-- The candidate frame allocates address 0, the end-of-list terminator. -/
def fnull : Heap := hsingle 0 1

private theorem qwf1 : qwf 2 [4, 6] := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem qrep1 : qrep 2 [4, 6] [7, 9] h1 := qheap_qrep _ _ _ qwf1 rfl (by simp)

/-! ## C1: overlap -/

/-- The compatibility check rejects the overlapping frame. -/
theorem overlap_rejected : ¬ hdisj h1 fbad := by
  intro hd
  rcases hd 3 with h | h
  · exact qrep_fp 2 [4, 6] [7, 9] h1 qrep1 3 (by decide) h
  · simp [fbad, hsingle] at h

/-- The claimed cell really changes after one rotation, so no assertion about it survives. -/
private theorem rot_changes_head_pointer : qstep 2 [4, 6] h1 3 = some 6 ∧ h1 3 = some 4 :=
  ⟨rfl, rfl⟩

/-- ...and the conclusion it would license is false. -/
theorem overlap_frame_not_preserved :
    cellsat [(3, 4)] h1 ∧ ¬ cellsat [(3, 4)] (qstep 2 [4, 6] h1) := by
  refine ⟨by simp [cellsat, rot_changes_head_pointer.2], fun H => ?_⟩
  have := H (3, 4) (.head _)
  rw [rot_changes_head_pointer.1] at this
  cases this

/-! ## C2: the null address -/

/-- The compatibility check rejects the null-allocating frame. -/
theorem null_frame_rejected : fnull 0 ≠ none := by simp [fnull, hsingle]

/-- ...and the extended heap is not a representation of the queue at all, although `hdisj`
holds: disjointness alone does not supply C2. -/
theorem null_frame_disjoint_but_bad :
    hdisj h1 fnull ∧ ¬ qrep 2 [4, 6] [7, 9] (hunion h1 fnull) := by
  refine ⟨fun x => ?_, fun hq => ?_⟩
  · by_cases hx : x = 0
    · subst hx; exact .inl (qrep_null _ _ _ _ qrep1)
    · exact .inr (by simp [fnull, hsingle]; omega)
  · have h0 := qrep_null _ _ _ _ hq
    rw [hunion_none _ _ _ (qrep_null _ _ _ _ qrep1)] at h0
    exact null_frame_rejected h0

/-! ## The two conditions are independent -/

theorem conditions_independent :
    (fbad 0 = none ∧ ¬ hdisj h1 fbad) ∧ (hdisj h1 fnull ∧ fnull 0 ≠ none) :=
  ⟨⟨rfl, overlap_rejected⟩, null_frame_disjoint_but_bad.1, null_frame_rejected⟩

end Examples.CSL.Overlap
