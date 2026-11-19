/- SPDX-License-Identifier: MIT -/
module

public import CTree.Interp.FoldCTree

/-!
# Internalizing external choices

`internalize` turns the events of `Ext` of a tree into branches: each event `e : Ext.I` becomes a
`branchS'` over its answers, and the remaining events of `E` are re-emitted
(← `Interp/Internalize.v`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)

variable {E C Ext : Effect.{u}} {R S : Type u}

/-- An external choice becomes a (stepping) branch. -/
def internalize_h (e : Ext.I) : CTree E (C ⊕ₑ Ext) (Ext.O e) := CTree.branchS' Ext e

/-- External choices become branches, other events are re-emitted. -/
def internalize_h' : (e : (Ext ⊕ₑ E).I) → CTree E (C ⊕ₑ Ext) ((Ext ⊕ₑ E).O e)
  | .inl e => internalize_h e
  | .inr e => CTree.trigger e

/-- Internalizes the events of `Ext` as branches. -/
def internalize : CTree (Ext ⊕ₑ E) C R → CTree E (C ⊕ₑ Ext) R := interp internalize_h'

theorem internalize_ret (r : R) : internalize (pure r : CTree (Ext ⊕ₑ E) C R) = pure r :=
  interp_ret _ r

theorem internalize_bind (t : CTree (Ext ⊕ₑ E) C R) (k : R → CTree (Ext ⊕ₑ E) C S) :
    internalize (t >>= k) = internalize t >>= fun x => internalize (k x) :=
  interp_bind _ t k

end CTree
