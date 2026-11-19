/- SPDX-License-Identifier: MIT -/
module

public import CTree.Core.Definitions

/-!
# Folding a choice tree into a monad

`foldM h g` implements the events of a tree with the handler `h` and its branches with the
scheduler `g`, in any monad with a loop operator (`ITree.MonadIter`), a stuck computation and an
observable step. Two special cases: `interp h` only implements the events and re-emits the
branches (`MonadBr`), `refine g` only implements the branches and re-emits the events
(`MonadTrigger`). `translate h` renames the events of a tree (← `Interp/Fold.v`).

Rocq's `fold` is `foldM` here, since `CTree.fold` is the coinductive constructor. Structural
equality is `=`, so the `Proper (equ …)` instances `interp_equ`, `refine_equ`, `translate_equ`
are not needed.
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)

variable {E F B C : Effect.{u}} {X : Type u}

section Fold
variable {M : Type u → Type u} [Monad M] [ITree.MonadIter M] [MonadStuck M] [MonadStep M]

/-- One iteration of `foldM`: run the head node of the tree, and continue with its child. -/
def foldStep (h : (e : E.I) → M (E.O e)) (g : (c : B.I) → M (B.O c)) (t : CTree E B X) :
    M (CTree E B X ⊕ X) :=
  match t.unfold with
  | .ret r => pure (.inr r)
  | .stuck => mstuck
  | .guard t => pure (.inl t)
  | .step t => (fun _ => .inl t) <$> mstep
  | .br c k => (fun x => .inl (k x)) <$> g c
  | .vis e k => (fun x => .inl (k x)) <$> h e

/-- Implements the events of a tree with `h` and its branches with `g`. -/
def foldM (h : (e : E.I) → M (E.O e)) (g : (c : B.I) → M (B.O c)) : CTree E B X → M X :=
  ITree.MonadIter.iter (foldStep h g)

/-- Implements the events of a tree, re-emitting its branches. -/
def interp [MonadBr B M] (h : (e : E.I) → M (E.O e)) : CTree E B X → M X :=
  foldM h mbr

/-- Implements the branches of a tree, re-emitting its events. -/
def refine [MonadTrigger E M] (g : (c : B.I) → M (B.O c)) : CTree E B X → M X :=
  foldM mtrigger g

end Fold

/-! ## `translate` -/

/-- Renames the events of a tree along `h`, which maps each event of `E` to an event of `F` and
converts its answers back (an `E ~> F` morphism that preserves answers, as in `Subeffect.map`). -/
def translate (h : (e : E.I) → (f : F.I) × (F.O f → E.O e)) (t : CTree E C X) : CTree F C X :=
  match t.unfold with
  | .ret x => pure x
  | .stuck => .stuck
  | .step t => .step (translate h t)
  | .guard t => .guard (translate h t)
  | .vis e k => .vis (h e).1 fun x => translate h (k ((h e).2 x))
  | .br c k => .br c fun x => translate h (k x)
partial_fixpoint

section Translate
variable (h : (e : E.I) → (f : F.I) × (F.O f → E.O e))

theorem unfold_translate (t : CTree E C X) :
    translate h t = match t.unfold with
      | .ret x => pure x
      | .stuck => .stuck
      | .step t => .step (translate h t)
      | .guard t => .guard (translate h t)
      | .vis e k => .vis (h e).1 fun x => translate h (k ((h e).2 x))
      | .br c k => .br c fun x => translate h (k x) := by
  rw [translate]

@[simp] theorem translate_ret (x : X) : translate h (pure x : CTree E C X) = pure x := by
  rw [unfold_translate]; simp
@[simp] theorem translate_stuck : translate h (.stuck : CTree E C X) = .stuck := by
  rw [unfold_translate]; simp
@[simp] theorem translate_guard (t : CTree E C X) :
    translate h t.guard = (translate h t).guard := by
  rw [unfold_translate]; simp
@[simp] theorem translate_step (t : CTree E C X) : translate h t.step = (translate h t).step := by
  rw [unfold_translate]; simp
@[simp] theorem translate_vis (e : E.I) (k : E.O e → CTree E C X) :
    translate h (.vis e k) = .vis (h e).1 fun x => translate h (k ((h e).2 x)) := by
  rw [unfold_translate]; simp
@[simp] theorem translate_br (c : C.I) (k : C.O c → CTree E C X) :
    translate h (.br c k) = .br c fun x => translate h (k x) := by
  rw [unfold_translate]; simp

end Translate

end CTree
