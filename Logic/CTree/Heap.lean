/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.CanStep
public import Logic.Interp.Heap

/-!
# Logical corollaries of the checked heap interpreter

The only genuinely logical fact about the heap handler: an out-of-footprint dereference cannot
step (← `CTree/Logic/Heap.v`).
-/

@[expose] public section
namespace Tisl
open CTree Tisl.Heap
open ITree (Effect)

section HeapNoStep
variable {F G B : Effect.{0}} {Sig : Type}
  (other : (e : G.I) → StateT (ManagedHeap × Sig) (CTree F B) (G.O e))

/-- An out-of-footprint read cannot step, regardless of its continuation. -/
theorem interp_heap_rd_nostep {X : Type} (a : Nat) (h allocs : Heap) (aux : Sig)
    (k : Nat → CTree (heapE ⊕ₑ G) B X) (w : World F) :
    h a = none →
    ¬ can_step
        (interp_state (h_sum heap_handler other) (heap_read a >>= k) ((h, allocs), aux)) w := by
  intro H
  rw [interp_state_bind, interp_heap_rd_stuck other a h allocs aux H]
  exact nostep_bind can_step_stuck

end HeapNoStep

end Tisl
