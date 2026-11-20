/- SPDX-License-Identifier: MIT -/
module
-- Lean-only module, no Rocq counterpart.

public import Lang.CoCSL.Asep

/-!
# Heap-view assertions shared by the separation regressions

`cell i a v`: lineage `i`'s local heap holds `v` at `a`. It is a view predicate, hence proper
and selection-stable.
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation
open Tisl Tisl.CSL CoCSL

def cell (i : Side) (a v : Nat) : hprop := fun c => (c.heap i).1 a = some v

theorem cell_view (i : Side) (a v : Nat) : view_pred (cell i a v) :=
  fun _ _ ⟨Hh, _⟩ H => ((Hh i).1 a).symm.trans H

theorem cell_proper (i : Side) (a v : Nat) : hproper (cell i a v) :=
  view_pred_proper _ (cell_view i a v)

theorem cell_stable (i : Side) (a v : Nat) : SelectionStable (cell i a v) :=
  view_selection_stable _ (cell_view i a v)

end Examples.CSL.Frame.Separation
