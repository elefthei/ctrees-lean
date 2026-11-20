/- SPDX-License-Identifier: MIT -/
module

public import Logic.World

/-!
# Kripke models

TICL is defined over any family of models `M E B X` with a transition relation `ktrans` between
pairs of a model and a world; models only step from non-terminal worlds (← `Logic/Kripke.v`).
-/

@[expose] public section
namespace Tisl
open ITree (Effect)

/-- A Kripke structure on the models `M E B X`. -/
class Kripke (M : Effect.{u} → Effect.{u} → Type u → Type u) (E B : Effect.{u}) where
  /-- `ktrans t w t' w'`: from world `w`, model `t` steps to `t'` reaching world `w'`. -/
  ktrans {X : Type u} : M E B X → World E → M E B X → World E → Prop
  /-- Models only step from non-terminal worlds. -/
  ktrans_not_done {X : Type u} {t t' : M E B X} {w w' : World E} : ktrans t w t' w' → NotDone w

export Kripke (ktrans ktrans_not_done)

variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {E B : Effect.{u}} [Kripke M E B]
  {X : Type u}

/-- `t` can step from world `w`. -/
def can_step (t : M E B X) (w : World E) : Prop := ∃ t' w', ktrans t w t' w'

theorem can_step_not_done {t : M E B X} {w : World E} (h : can_step t w) : NotDone w :=
  let ⟨_, _, h⟩ := h; ktrans_not_done h

/-- `ktrans` with the successor first, the orientation `Acc`/`WellFounded` expect. -/
def kripke_step (next current : M E B X × World E) : Prop :=
  ktrans current.1 current.2 next.1 next.2

end Tisl
