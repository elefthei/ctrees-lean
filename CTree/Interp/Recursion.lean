/- SPDX-License-Identifier: MIT -/
module

public import CTree.Interp.Fold

/-!
# General recursion (← `Interp/Recursion.v`)

The effect `D` gives the signature of a set of mutually recursive functions; a handler
`ctx : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d)` gives their bodies, which may call each other by
triggering `Sum.inl d`. `interp_mrec ctx` ties the knot, `mrec ctx` runs one function, and
`rec`/`call` specialize this to a single recursive function `X → Y` (effect `callE X Y`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)

variable {D E B : Effect.{u}} {R : Type u}

/-! ## Mutual recursion -/

/-- Interpret a tree in the context of a mutually recursive definition `ctx`. -/
def interp_mrec (ctx : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d)) :
    CTree (D ⊕ₑ E) B R → CTree E B R :=
  CTree.iter fun t =>
    match t.unfold with
    | .ret r => pure (.inr r)
    | .stuck => .stuck
    | .step t => .step (pure (.inl t))
    | .guard t => pure (.inl t)
    | .vis (.inl d) k => pure (.inl (ctx d >>= k))
    | .vis (.inr e) k => .vis e fun x => pure (.inl (k x))
    | .br c k => .br c fun x => pure (.inl (k x))

/-- Unfold a mutually recursive definition into separate trees, resolving the mutual
references. -/
def mrec (ctx : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d)) (d : D.I) : CTree E B (D.O d) :=
  interp_mrec ctx (ctx d)

/-- Make a recursive call in the handler argument of `mrec`. -/
def trigger_inl1 (d : D.I) : CTree (D ⊕ₑ E) B (D.O d) := CTree.trigger (E := D ⊕ₑ E) (.inl d)

/-! ## Simple recursion -/

/-- Calls of a function `A → B`. -/
@[implicit_reducible]
def callE (A Y : Type u) : Effect.{u} := ⟨A, fun _ => Y⟩

unif_hint (A Y : Type u) (a : A) where |- (callE A Y).O a ≟ Y

/-- The argument of a call (Rocq `unCall`; a call is its argument). -/
def unCall {A Y : Type u} (e : (callE A Y).I) : A := e

/-- Lift a function on `A` to a handler of `callE A Y`. -/
def calling {A Y : Type u} {F : Type u → Type u} (f : A → F Y) :
    (e : (callE A Y).I) → F ((callE A Y).O e) := f

/-- `calling` specialized to choice trees. -/
def calling' {X Y : Type u} {F B : Effect.{u}} (f : X → CTree F B Y) :
    (e : (callE X Y).I) → CTree F B ((callE X Y).O e) := calling f

/-- Interpret a single recursive definition. -/
def rec {X Y : Type u} (body : X → CTree (callE X Y ⊕ₑ E) B Y) (x : X) : CTree E B Y :=
  mrec (calling body) x

/-- The recursive call event, for use in the body passed to `rec`. -/
def call {X Y : Type u} (x : X) : CTree (callE X Y ⊕ₑ E) B Y :=
  CTree.trigger (E := callE X Y ⊕ₑ E) (.inl x)

/-! ## Example: mutually recursive `even`/`odd` (from the Rocq module comment) -/

private inductive EvenOdd : Type u
  | even (n : Nat) | odd (n : Nat)

@[implicit_reducible] private def evenOddE : Effect.{u} := ⟨EvenOdd, fun _ => ULift Bool⟩

private noncomputable def evenOddDef (d : evenOddE.{u}.I) :
    CTree (evenOddE ⊕ₑ E) B (evenOddE.O d) :=
  match d with
  | .even 0 => pure ⟨true⟩
  | .even (m + 1) => CTree.trigger (E := evenOddE ⊕ₑ E) (.inl (EvenOdd.odd m))
  | .odd 0 => pure ⟨false⟩
  | .odd (m + 1) => CTree.trigger (E := evenOddE ⊕ₑ E) (.inl (EvenOdd.even m))

private noncomputable def even (n : Nat) : CTree E B (ULift Bool) :=
  mrec evenOddDef (EvenOdd.even n)

end CTree
