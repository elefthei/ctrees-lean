/- SPDX-License-Identifier: MIT -/
module

public import CTree
public import Logic.Utils.Vectors

/-!
# Cooperative concurrency events

Scheduling points (`yieldE`), thread-local fork choices (`forkE`), selected pool slots (`schedE`),
their triggers, and the types of threads, scheduled computations and pools
(← `Events/YieldE.v`, `CTree/Events/Yield.v`).
-/

@[expose] public section
namespace Tisl
open CTree
open ITree (Effect)

/-- Cooperative scheduling point (Rocq `Yield : yieldE unit`). -/
@[implicit_reducible] def yieldE : Effect.{0} := ⟨PUnit, fun _ => PUnit⟩
unif_hint (x : yieldE.I) where |- yieldE.O x ≟ PUnit

/-- Thread-local fork choice (Rocq `Fork : forkE bool`). -/
@[implicit_reducible] def forkE : Effect.{0} := ⟨PUnit, fun _ => Bool⟩
unif_hint (x : forkE.I) where |- forkE.O x ≟ Bool

/-- The zero-based slot selected at a scheduling boundary (Rocq `Scheduled n : schedE unit`). -/
@[implicit_reducible] def schedE : Effect.{0} := ⟨Nat, fun _ => PUnit⟩
unif_hint (x : schedE.I) where |- schedE.O x ≟ PUnit

variable {E B : Effect.{0}}

/-- A `yield` event node. -/
def yield [yieldE -< E] : CTree E B PUnit := CTree.trigger' yieldE ⟨⟩

/-- A `fork` event node. -/
def fork [forkE -< E] : CTree E B Bool := CTree.trigger' forkE ⟨⟩

/-- A runnable source thread may yield, fork, or perform user effects. -/
abbrev Thread (E B : Effect.{0}) := CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B PUnit

/-- A scheduled computation exposes user effects and selected pool slots. -/
abbrev Completed (E B : Effect.{0}) := CTree (E ⊕ₑ schedE) B PUnit

/-- A policy-scheduled pool exposes scheduling decisions and user events. -/
abbrev Scheduled (E B : Effect.{0}) := CTree (schedE ⊕ₑ E) B PUnit

/-- Finite thread pools. -/
abbrev Pool (E B : Effect.{0}) (n : Nat) := Vector (Thread E B) n

end Tisl
