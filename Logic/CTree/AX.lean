/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.CanStep

/-!
# Forall-next on ctrees

Structural rules for the forall-next modality `φ AN ψ` on ctrees, by the head constructor of the
tree; the target `ψ` ranges over formulas of every index (← `CTree/Logic/AX.v`).
-/

@[expose] public section
namespace Tisl
open CTree Notation
open ITree (Effect)
open Yield (br_alts)

section BasicLemmas
variable {E B : Effect.{u}} {X : Type u} {i : Option (Type u)} {w : World E} {φ : TiclL E}
  {ψ : Ticl E i}

/-- Stuck has no next step, independently of the target formula's index. -/
theorem an_stuck : ¬ entails (φ AN ψ) (CTree.stuck : CTree E B X) w :=
  fun h => can_step_stuck h.2.1

/-- Hidden branching requires an actual transition from at least one branch. -/
theorem an_br {c : B.I} {k : B.O c → CTree E B X} (hφ : entails φ (CTree.br c k) w)
    (hs : ∃ y, can_step (k y) w) (hk : ∀ y t' w', ktrans (k y) w t' w' → entails ψ t' w') :
    entails (φ AN ψ) (CTree.br c k) w :=
  ⟨hφ, can_step_br.2 hs, fun t' w' tr => let ⟨y, tr⟩ := ktrans_br.1 tr; hk y t' w' tr⟩

/-- Policy alternatives crawl through an actual transition of an alternative. -/
theorem an_br_alts [Bn -< B] [LawfulSubeffect Bn B] {m : Nat} {k : Fin (m + 1) → CTree E B X}
    (hφ : entails φ (br_alts m k) w) (hs : ∃ a, can_step (k a) w)
    (hk : ∀ a t' w', ktrans (k a) w t' w' → entails ψ t' w') :
    entails (φ AN ψ) (br_alts m k) w :=
  ⟨hφ, can_step_br_alts.2 hs, fun t' w' tr => let ⟨a, tr⟩ := ktrans_br_alts.1 tr; hk a t' w' tr⟩

/-- Visible branching retains an explicit inhabitant to witness progress. -/
theorem an_brS {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) :
    entails (φ AN ψ) (CTree.brS c k) w ↔
      entails φ (CTree.brS c k) w ∧ ∀ y, entails ψ (k y) w := by
  constructor
  · rintro ⟨hφ, hs, hk⟩
    exact ⟨hφ, fun y' => hk _ _ (ktrans_brS.2 ⟨y', rfl, rfl, can_step_not_done hs⟩)⟩
  · rintro ⟨hφ, hk⟩
    refine ⟨hφ, (can_step_brS y).2 (ticl_not_done φ hφ), fun t' w' tr => ?_⟩
    obtain ⟨y', rfl, rfl, -⟩ := ktrans_brS.1 tr
    exact hk y'

/-- Visible step iff lemma for the forall-next modality. -/
theorem an_step {t : CTree E B X} :
    entails (φ AN ψ) (CTree.step t) w ↔ entails φ (CTree.step t) w ∧ entails ψ t w := by
  constructor
  · rintro ⟨hφ, hs, hk⟩
    exact ⟨hφ, hk _ _ (ktrans_step.2 ⟨rfl, rfl, can_step_not_done hs⟩)⟩
  · rintro ⟨hφ, hψ⟩
    refine ⟨hφ, can_step_step.2 (ticl_not_done φ hφ), fun t' w' tr => ?_⟩
    obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
    exact hψ

/-- Visible events retain an explicit answer inhabitant to witness progress. -/
theorem an_vis {e : E.I} {k : E.O e → CTree E B X} (v : E.O e) :
    entails (φ AN ψ) (CTree.vis e k) w ↔
      entails φ (CTree.vis e k) w ∧ ∀ v, entails ψ (k v) (.obs e v) := by
  constructor
  · rintro ⟨hφ, hs, hk⟩
    exact ⟨hφ, fun v' => hk _ _ (ktrans_vis.2 ⟨v', rfl, rfl, can_step_not_done hs⟩)⟩
  · rintro ⟨hφ, hk⟩
    refine ⟨hφ, (can_step_vis v).2 (ticl_not_done φ hφ), fun t' w' tr => ?_⟩
    obtain ⟨v', rfl, rfl, -⟩ := ktrans_vis.1 tr
    exact hk v'

/-- Completion successors cannot satisfy a formula of any index. -/
theorem an_ret {r : X} : ¬ entails (φ AN ψ) (pure r : CTree E B X) w := by
  rintro ⟨-, ⟨t', w', tr⟩, hk⟩
  have h := ticl_not_done ψ (hk t' w' tr)
  cases ktrans_not_done tr with
  | pure => obtain ⟨rfl, -⟩ := ktrans_done.1 tr; cases h
  | obs e v => obtain ⟨rfl, -⟩ := ktrans_finish.1 tr; cases h

end BasicLemmas

end Tisl
