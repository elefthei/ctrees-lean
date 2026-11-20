/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Representation

/-!
# Queue rotation, independent of its observation alphabet

One rotation of the heap-backed queue at `hdr` as nine heap instructions plus an
alphabet-specific emission, its log trace `queue_turn_logs`, and the correspondence
`queue_turn_spec` with the pure surgery `rot_heap` under the CSL handler `sh`
(← `examples/CSL/Queue/Operations.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Operations
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Examples.CSL.Queue.Representation
open ITree (Effect)

/-- The memory operations of one rotation; `emit_value` chooses the observation alphabet. -/
def queue_turn {E B : Effect.{0}} [heapE -< E] {X : Type} (emit_value : Nat → CTree E B PUnit)
    (hdr : Nat) (tail : CTree E B X) : CTree E B X :=
  heap_read (hdr + 1) >>= fun a =>
  heap_read a >>= fun value =>
  emit_value value >>= fun _ =>
  heap_read (a + 1) >>= fun next =>
  heap_write (hdr + 1) next >>= fun _ =>
  heap_read hdr >>= fun last =>
  heap_write ((if next == 0 then hdr else last) + 1) a >>= fun _ =>
  heap_write (a + 1) 0 >>= fun _ =>
  heap_write hdr a >>= fun _ =>
  tail

/-- The observations of one rotation: the emission, then the four post-write heaps. -/
def queue_turn_logs {A : Type} (event : CSLObs A) (hdr a next last : Nat)
    (memory : ManagedHeap) : List (CSLObs A) :=
  let h0 := memory.1
  let al := memory.2
  let h1 := upd h0 (hdr + 1) next
  let h2 := upd h1 ((if next == 0 then hdr else last) + 1) a
  let h3 := upd h2 (a + 1) 0
  let h4 := upd h3 hdr a
  [event, .heap (h1, al), .heap (h2, al), .heap (h3, al), .heap (h4, al)]

theorem queue_turn_equ {E B : Effect.{0}} [heapE -< E] {X : Type}
    (emit_value : Nat → CTree E B PUnit) (hdr : Nat) (t u : CTree E B X) :
    t = u → queue_turn emit_value hdr t = queue_turn emit_value hdr u :=
  congrArg _

theorem queue_turn_bind {E B : Effect.{0}} [heapE -< E] {X Y : Type}
    (emit_value : Nat → CTree E B PUnit) (hdr : Nat) (tail : CTree E B X)
    (k : X → CTree E B Y) :
    (queue_turn emit_value hdr tail >>= k) = queue_turn emit_value hdr (tail >>= k) := by
  simp only [queue_turn, bind_assoc]

/-- The rotation correspondence, stated at the CSL handler `sh` for any emission whose
interpretation logs one observation and advances the counter. -/
theorem queue_turn_spec {A X : Type}
    (emit_value : Nat → CTree (heapE ⊕ₑ stateE Ctx ⊕ₑ writerE A) Bn PUnit)
    (observe_value : Nat → Nat → CSLObs A)
    (Emit : ∀ value h allocs ctx c (tail : CTree (heapE ⊕ₑ stateE Ctx ⊕ₑ writerE A) Bn X),
      interp_state sh (emit_value value >>= fun _ => tail) ((h, allocs), (ctx, c)) ~
        (log (observe_value value c) >>= fun _ =>
          interp_state sh tail ((h, allocs), (ctx, c + 1))))
    (hdr a : Nat) (ns : List Nat) (value : Nat) (values : List Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) (tail : CTree (heapE ⊕ₑ stateE Ctx ⊕ₑ writerE A) Bn X) :
    qrep hdr (a :: ns) (value :: values) h →
    interp_state sh (queue_turn emit_value hdr tail) ((h, allocs), (ctx, c)) ~
      emit_list (queue_turn_logs (observe_value value c) hdr a (ns.headD 0)
          ((a :: ns).getLastD 0) (h, allocs))
        (interp_state sh tail
          ((rot_heap hdr a (ns.headD 0) (zof hdr ns) h, allocs), (ctx, c + 1))) := by
  intro Hq
  let other : (e : (stateE Ctx ⊕ₑ writerE A).I) → StateT SSig (ctreeW (CSLObs A) Bn) _ :=
    h_sum csl_context_handler csl_emit_handler
  have Hq' := Hq
  obtain ⟨Hwf, Hhd, Htl, Hch, -, -⟩ := Hq'
  obtain ⟨Ha, Hsa, -⟩ := (chain_cons _ _ _ _ _ _).1 Hch
  have Hzdom := qrep_zof_dom _ _ _ _ _ _ Hq
  have Hhdrdom : h hdr ≠ none := by
    have : h hdr = some ((a :: ns).getLastD 0) := Htl
    simp [this]
  have Hsadom : h (a + 1) ≠ none := by simp [Hsa]
  have Hshdrdom : h (hdr + 1) ≠ none := by simp [Hhd]
  obtain ⟨Hha, Hsha, Hhsa, Hshsa, Hhshdr⟩ := qwf_neqs _ _ _ Hwf
  have Hread_hdr : upd h (hdr + 1) (ns.headD 0) hdr = some ((a :: ns).getLastD 0) := by
    rw [upd_neq _ _ _ _ (by omega)]; exact Htl
  simp only [queue_turn, queue_turn_logs, emit_list_cons, emit_list_nil]
  rw [zof_compute hdr a ns Hwf]
  refine sbisim_trans (interp_heapW_rd CSLObs.heap other (hdr + 1) h allocs (ctx, c) a _ Hhd) ?_
  refine sbisim_trans (interp_heapW_rd CSLObs.heap other a h allocs (ctx, c) value _ Ha) ?_
  refine sbisim_trans (Emit _ _ _ _ _ _) ?_
  rw [log_vis]; refine sb_vis _ fun _ => ?_
  refine sbisim_trans
    (interp_heapW_rd CSLObs.heap other (a + 1) h allocs (ctx, c + 1) (ns.headD 0) _ Hsa) ?_
  refine sbisim_trans (interp_heapW_wr_present CSLObs.heap other (hdr + 1) h allocs (ctx, c + 1)
    (ns.headD 0) _ Hshdrdom) ?_
  rw [log_vis]; refine sb_vis _ fun _ => ?_
  refine sbisim_trans (interp_heapW_rd CSLObs.heap other hdr (upd h (hdr + 1) (ns.headD 0)) allocs
    (ctx, c + 1) ((a :: ns).getLastD 0) _ Hread_hdr) ?_
  simp only [zof_compute hdr a ns Hwf]
  refine sbisim_trans (interp_heapW_wr_present CSLObs.heap other (zof hdr ns + 1) _ allocs
    (ctx, c + 1) a _ (upd_mono _ _ _ _ Hzdom)) ?_
  rw [log_vis]; refine sb_vis _ fun _ => ?_
  refine sbisim_trans (interp_heapW_wr_present CSLObs.heap other (a + 1) _ allocs (ctx, c + 1) 0 _
    (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hsadom))) ?_
  rw [log_vis]; refine sb_vis _ fun _ => ?_
  refine sbisim_trans (interp_heapW_wr_present CSLObs.heap other hdr _ allocs (ctx, c + 1) a _
    (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hhdrdom)))) ?_
  rw [log_vis]; refine sb_vis _ fun _ => ?_
  exact sbisim_refl _

-- Not ported: `log_vis` (already `Tisl.log_vis` in `Logic/CTree/Trace.lean`).

end Examples.CSL.Queue.Operations
