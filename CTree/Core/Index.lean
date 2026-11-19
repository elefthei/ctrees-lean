/- SPDX-License-Identifier: MIT -/
module

public import ITree.Effect

/-!
# Branching indices

Common branching interfaces, as `Effect`s whose inputs index the branches and whose outputs are
the branch choices (← `Core/Index.v`).
-/

@[expose] public section
namespace CTree
open ITree (Effect)

/-- Nullary branching, encoding stuck processes. -/
@[implicit_reducible] def B0 : Effect.{u} := ⟨PUnit, fun _ => PEmpty⟩
unif_hint (x : B0.{u}.I) where |- B0.{u}.O x ≟ PEmpty.{u + 1}

/-- Unary branching, encoding taus/fuel/guards. -/
@[implicit_reducible] def B1 : Effect.{u} := ⟨PUnit, fun _ => PUnit⟩
unif_hint (x : B1.{u}.I) where |- B1.{u}.O x ≟ PUnit.{u + 1}

/-- Binary branching. -/
@[implicit_reducible] def B2 : Effect.{u} := ⟨PUnit, fun _ => ULift Bool⟩
unif_hint (x : B2.{u}.I) where |- B2.{u}.O x ≟ ULift.{u} Bool

/-- Ternary branching (Rocq `T3`: `t31 ↦ 0`, `t32 ↦ 1`, `t33 ↦ 2`). -/
@[implicit_reducible] def B3 : Effect.{u} := ⟨PUnit, fun _ => ULift (Fin 3)⟩
unif_hint (x : B3.{u}.I) where |- B3.{u}.O x ≟ ULift.{u} (Fin 3)

/-- Quaternary branching (Rocq `T4`: `t41 ↦ 0`, …, `t44 ↦ 3`). -/
@[implicit_reducible] def B4 : Effect.{u} := ⟨PUnit, fun _ => ULift (Fin 4)⟩
unif_hint (x : B4.{u}.I) where |- B4.{u}.O x ≟ ULift.{u} (Fin 4)

/-- Finite unbounded branching: the index `n` offers `n` branches. -/
@[implicit_reducible] def Bn : Effect.{u} := ⟨ULift Nat, fun n => ULift (Fin n.down)⟩
unif_hint (x : Bn.{u}.I) where |- Bn.{u}.O x ≟ ULift.{u} (Fin x.down)

/-- Countable branching. -/
@[implicit_reducible] def BN : Effect.{u} := ⟨PUnit, fun _ => ULift Nat⟩
unif_hint (x : BN.{u}.I) where |- BN.{u}.O x ≟ ULift.{u} Nat

abbrev B01 : Effect.{u} := B0 ⊕ₑ B1
abbrev B02 : Effect.{u} := B0 ⊕ₑ B1 ⊕ₑ B2

end CTree
