/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Operations

/-!
# Checked sequential queue rotation with occurrence-indexed observations

The rotating queue over the CSL effects at payload `Nat`: a checked heap (out-of-footprint
accesses are stuck), every mutation logged as a heap snapshot, and occurrence-indexed payload
emissions (← `examples/CSL/Queue/Sequential.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Sequential
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Examples.CSL.Queue.Representation
  Examples.CSL.Queue.Operations
open ITree (Effect)

/-- The queue's events: heap, (unused) context, and payload emission. -/
abbrev qE : Effect.{0} := heapE ⊕ₑ stateE Ctx ⊕ₑ writerE Nat

/-- Payload emission, the example-specific instruction. -/
def emit (v : Nat) : CTree qE Bn PUnit := CTree.trigger (E := qE) (.inr (.inr v))

/-- One rotation: read and emit the head payload, detach it and re-link it at the tail. -/
def rot_body (hdr : Nat) : CTree qE Bn (PUnit ⊕ PUnit) := queue_turn emit hdr (pure (.inl ⟨⟩))

def rotate (hdr : Nat) : CTree qE Bn PUnit := CTree.iter (fun _ : PUnit => rot_body hdr) ⟨⟩

/-- The rotation interpreted with the CSL handler at payload `Nat`; the counter indexes the
observations only. -/
def run (hdr : Nat) (s : SSig) : ctreeW (CSLObs Nat) Bn (PUnit × SSig) :=
  interp_state (sh (A := Nat)) (rotate hdr) s

/-- One rotation emits its payload and the four post-write heaps, then returns the rotated
representation. -/
theorem rot_body_spec (hdr a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    qrep hdr (a :: ns) (v :: vs) h →
    interp_state (sh (A := Nat)) (rot_body hdr) ((h, allocs), (ctx, c)) ~
      (emit_list (queue_turn_logs (.emit (stamp v c)) hdr a (ns.headD 0) ((a :: ns).getLastD 0)
          (h, allocs))
        (pure (.inl ⟨⟩, ((rot_heap hdr a (ns.headD 0) (zof hdr ns) h, allocs), (ctx, c + 1))))
        : ctreeW (CSLObs Nat) Bn ((PUnit ⊕ PUnit) × SSig)) := by
  intro Hq
  refine sbisim_trans (queue_turn_spec emit (fun v c => .emit (stamp v c))
    (fun _ _ _ _ _ _ => interp_csl_emit _ _ _ _ _) hdr a ns v vs h allocs ctx c _ Hq) ?_
  rw [interp_state_ret]
  exact sbisim_refl _

end Examples.CSL.Queue.Sequential
