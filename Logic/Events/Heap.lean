/- SPDX-License-Identifier: MIT -/
module

public import CTree

/-!
# Heap events

The heap effect (read, write, allocate, free, compare-and-swap) and its triggers
(← `Events/HeapE.v`, `CTree/Events/Heap.v`). The heap layer lives at universe 0.
-/

@[expose] public section
namespace Tisl
open CTree
open ITree (Effect)

/-- Heap operations (Rocq `HRead`, `HWrite`, `HAlloc`, `HFree`, `HCAS`). -/
inductive HeapOp
  | read (a : Nat)
  | write (a v : Nat)
  | alloc (size : Nat)
  | free (a : Nat)
  | cas (a expected desired : Nat)

/-- The heap effect: reads and allocations answer a `Nat`, compare-and-swap a `Bool`. -/
@[implicit_reducible] def heapE : Effect.{0} :=
  ⟨HeapOp, fun | .read _ => Nat | .write .. => PUnit | .alloc _ => Nat | .free _ => PUnit
               | .cas .. => Bool⟩
unif_hint (a : Nat) where |- heapE.O (HeapOp.read a) ≟ Nat
unif_hint (a v : Nat) where |- heapE.O (HeapOp.write a v) ≟ PUnit
unif_hint (n : Nat) where |- heapE.O (HeapOp.alloc n) ≟ Nat
unif_hint (a : Nat) where |- heapE.O (HeapOp.free a) ≟ PUnit
unif_hint (a e d : Nat) where |- heapE.O (HeapOp.cas a e d) ≟ Bool

variable {E B : Effect.{0}} [heapE -< E]

def heap_read (a : Nat) : CTree E B Nat := CTree.trigger' heapE (.read a)
def heap_write (a v : Nat) : CTree E B PUnit := CTree.trigger' heapE (.write a v)
def heap_alloc (size : Nat) : CTree E B Nat := CTree.trigger' heapE (.alloc size)
def heap_free (a : Nat) : CTree E B PUnit := CTree.trigger' heapE (.free a)
def heap_cas (a expected desired : Nat) : CTree E B Bool :=
  CTree.trigger' heapE (.cas a expected desired)

end Tisl
