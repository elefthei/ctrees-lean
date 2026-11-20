/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.AX
public import Logic.CTree.AF
public import Logic.CTree.AG
public import Logic.CTree.EX
public import Logic.CTree.EF
public import Logic.CTree.EG

/-!
# Return nodes and prefix formulas

Return nodes are indistinguishable by prefix formulas, whatever value and type they return
(← `CTree/Logic/Ret.v`).
-/

@[expose] public section
namespace Tisl
open CTree Notation
open ITree (Effect)

section RetLemmas
variable {E B : Effect.{u}} {X Y : Type u} {w : World E}

private theorem ret_impl {i : Option (Type u)} (φ : Ticl E i) (hi : i = none) {x : X} {y : Y}
    (h : entails φ (pure x : CTree E B X) w) : entails φ (pure y : CTree E B Y) w := by
  induction φ generalizing w with
  | now p => exact h
  | ret p => cases hi
  | cu q p r ihp ihr =>
    cases q
    · rcases au_ret.2 h with h | h
      · exact au_ret.1 (.inl (ihr hi h))
      · exact (an_ret h).elim
    · rcases eu_ret.2 h with h | h
      · exact eu_ret.1 (.inl (ihr hi h))
      · exact (en_ret h).elim
  | cx q p r =>
    cases q
    · exact (an_ret h).elim
    · exact (en_ret h).elim
  | cg q p =>
    cases q
    · exact (ag_ret h).elim
    · exact (eg_ret h).elim
  | and p r ihp ihr => exact ⟨ihp hi h.1, ihr hi h.2⟩
  | or p r ihp ihr => exact h.imp (ihp hi) (ihr hi)

/-- Return nodes are prefix-formula equivalent, regardless of the returned value. -/
theorem ticll_ret_equiv {x : X} {y : Y} {φ : TiclL E} :
    entails φ (pure x : CTree E B X) w ↔ entails φ (pure y : CTree E B Y) w :=
  ⟨ret_impl φ rfl, ret_impl φ rfl⟩

end RetLemmas

-- Not ported: nothing.

end Tisl
