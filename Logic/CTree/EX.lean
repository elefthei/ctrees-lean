/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.CanStep
public import Logic.Events.Writer

/-!
# The exists-next modality on ctrees

Structural rules for `φ EN ψ` on ctrees: stuck trees and returns have no next step, hidden branches
keep a transition of a selected branch, visible branches/steps/events expose one successor
(← `CTree/Logic/EX.v`).
-/

@[expose] public section
namespace Tisl
open CTree Notation
open ITree (Effect)

section BasicLemmas
variable {E B : Effect.{u}} {X : Type u} {i : Option (Type u)} {w : World E} {φ : TiclL E}
  {ψ : Ticl E i}

/-- A stuck tree does not satisfy `φ EN ψ`, at either formula mode. -/
theorem en_stuck : ¬ entails (φ EN ψ) (.stuck : CTree E B X) w :=
  fun h => let ⟨_, _, _, tr, _⟩ := (ticl_en _ _).1 h; ktrans_stuck tr

/-- Hidden branching retains a transition from the selected branch. -/
theorem en_br {c : B.I} {k : B.O c → CTree E B X} :
    entails (φ EN ψ) (CTree.br c k) w ↔
      entails φ (CTree.br c k) w ∧ ∃ y t' w', ktrans (k y) w t' w' ∧ entails ψ t' w' :=
  ⟨fun ⟨hφ, t', w', tr, h⟩ => let ⟨y, tr⟩ := ktrans_br.1 tr; ⟨hφ, y, t', w', tr, h⟩,
   fun ⟨hφ, y, t', w', tr, h⟩ => ⟨hφ, t', w', ktrans_br.2 ⟨y, tr⟩, h⟩⟩

/-- Visible branching exposes a successor satisfying the indexed target. -/
theorem en_brS {c : B.I} {k : B.O c → CTree E B X} :
    entails (φ EN ψ) (CTree.brS c k) w ↔
      entails φ (CTree.brS c k) w ∧ ∃ y, entails ψ (k y) w := by
  refine ⟨fun ⟨hφ, t', w', tr, h⟩ => ?_, fun ⟨hφ, y, h⟩ => ?_⟩
  · obtain ⟨y, rfl, rfl, -⟩ := ktrans_brS.1 tr
    exact ⟨hφ, y, h⟩
  · exact ⟨hφ, k y, w, ktrans_brS.2 ⟨y, rfl, rfl, ticl_not_done φ hφ⟩, h⟩

/-- A visible step exposes its continuation at the same world. -/
theorem en_step {t : CTree E B X} :
    entails (φ EN ψ) (CTree.step t) w ↔ entails φ (CTree.step t) w ∧ entails ψ t w := by
  refine ⟨fun ⟨hφ, t', w', tr, h⟩ => ?_, fun ⟨hφ, h⟩ => ?_⟩
  · obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
    exact ⟨hφ, h⟩
  · exact ⟨hφ, t, w, ktrans_step.2 ⟨rfl, rfl, ticl_not_done φ hφ⟩, h⟩

/-- Visible events expose the selected response and its observation world. -/
theorem en_vis {e : E.I} {k : E.O e → CTree E B X} :
    entails (φ EN ψ) (CTree.vis e k) w ↔
      entails φ (CTree.vis e k) w ∧ ∃ v, entails ψ (k v) (.obs e v) := by
  refine ⟨fun ⟨hφ, t', w', tr, h⟩ => ?_, fun ⟨hφ, v, h⟩ => ?_⟩
  · obtain ⟨v, rfl, rfl, -⟩ := ktrans_vis.1 tr
    exact ⟨hφ, v, h⟩
  · exact ⟨hφ, k v, .obs e v, ktrans_vis.2 ⟨v, rfl, rfl, ticl_not_done φ hφ⟩, h⟩

/-- Return completion cannot satisfy an indexed next target. -/
theorem en_ret {r : X} : ¬ entails (φ EN ψ) (pure r : CTree E B X) w := by
  intro ⟨hφ, t', w', tr, h⟩
  have := ticl_not_done ψ h
  cases ticl_not_done φ hφ
  · obtain ⟨rfl, -⟩ := ktrans_done.1 tr; cases this
  · obtain ⟨rfl, -⟩ := ktrans_finish.1 tr; cases this

end BasicLemmas

section WriterLemmas
variable {B : Effect.{u}} {S : Type u} {w : World (writerE S)}

/-- Convenience lemma for the `EX` operator and the `log` event. -/
theorem exr_log {x : S} (hd : NotDone w) :
    entails (EX (ret= PUnit.unit (.obs (E := writerE S) x ⟨⟩))) (log x : ctreeW S B PUnit) w :=
  en_vis.2 ⟨⟨trivial, hd⟩, ⟨⟩, ret_ret (.obs _ _) ⟨rfl, rfl⟩⟩

end WriterLemmas

end Tisl
