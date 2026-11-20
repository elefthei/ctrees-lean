/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.AX

/-!
# Forall-until on ctrees

Structural rules for the forall-until modality `φ AU ψ` and forall-eventually `AF ψ` on ctrees,
by the head constructor of the tree (← `CTree/Logic/AF.v`).
-/

@[expose] public section
namespace Tisl
open CTree Notation
open ITree (Effect)
open Yield (br_alts)

section BasicLemmas
variable {E B : Effect.{u}} {X : Type u} {i : Option (Type u)} {w : World E} {φ : TiclL E}
  {ψ : Ticl E i}

/-- Stuckness preserves precisely the until target. -/
theorem au_stuck :
    entails ψ (CTree.stuck : CTree E B X) w ↔ entails (φ AU ψ) (CTree.stuck : CTree E B X) w :=
  ⟨.matchA, fun h => match (h : Auc _ _ _ _) with
    | .matchA h => h
    | .stepA _ hs _ => (can_step_stuck hs).elim⟩

/-- Return-until retains the target-or-next decomposition. -/
theorem au_ret {r : X} :
    entails (ψ ∨ₜ (φ AN ψ)) (pure r : CTree E B X) w ↔
      entails (φ AU ψ) (pure r : CTree E B X) w := by
  constructor
  · rintro (h | h)
    · exact .matchA h
    · exact ticl_an_au h
  · intro h
    match (h : Auc _ _ _ _) with
    | .matchA h => exact .inl h
    | .stepA hφ hs hk =>
      refine .inr ⟨hφ, hs, fun t' w' tr => ?_⟩
      obtain ⟨_, tr', -⟩ := ktrans_trans.1 tr
      have h := hk t' w' tr
      rw [(trans_ret_inv tr').1] at h ⊢
      exact au_stuck (φ := φ).2 h

/-- Hidden branching requires actual transitions from its branches. -/
theorem au_br {c : B.I} {k : B.O c → CTree E B X} (hφ : entails φ (CTree.br c k) w)
    (hs : ∃ y, can_step (k y) w)
    (hk : ∀ y t' w', ktrans (k y) w t' w' → entails (φ AU ψ) t' w') :
    entails (φ AU ψ) (CTree.br c k) w :=
  Auc.stepA' (an_br hφ hs hk)

/-- Until through a nonempty family of policy alternatives. -/
theorem au_br_alts [Bn -< B] [LawfulSubeffect Bn B] {m : Nat} {k : Fin (m + 1) → CTree E B X}
    (hφ : entails φ (br_alts m k) w) (hs : ∃ a, can_step (k a) w)
    (hk : ∀ a t' w', ktrans (k a) w t' w' → entails (φ AU ψ) t' w') :
    entails (φ AU ψ) (br_alts m k) w :=
  Auc.stepA' (an_br_alts hφ hs hk)

/-- Visible branching keeps an explicit inhabitant to witness progress. -/
theorem au_brS {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) :
    (entails ψ (CTree.brS c k) w ∨
      entails φ (CTree.brS c k) w ∧ ∀ y, entails (φ AU ψ) (k y) w) ↔
      entails (φ AU ψ) (CTree.brS c k) w :=
  (auc_unfold.trans (or_congr_right (an_brS (φ := φ) (ψ := φ AU ψ) y))).symm

/-- Visible step iff lemma for the forall-until modality. -/
theorem au_step {t : CTree E B X} :
    (entails ψ (CTree.step t) w ∨
      entails φ (CTree.step t) w ∧ entails (φ AU ψ) t w) ↔
      entails (φ AU ψ) (CTree.step t) w :=
  (auc_unfold.trans (or_congr_right (an_step (φ := φ) (ψ := φ AU ψ)))).symm

/-- Visible events keep an explicit answer inhabitant to witness progress. -/
theorem au_vis {e : E.I} {k : E.O e → CTree E B X} (v : E.O e) :
    (entails ψ (CTree.vis e k) w ∨
      entails φ (CTree.vis e k) w ∧ ∀ v, entails (φ AU ψ) (k v) (.obs e v)) ↔
      entails (φ AU ψ) (CTree.vis e k) w :=
  (auc_unfold.trans (or_congr_right (an_vis (φ := φ) (ψ := φ AU ψ) v))).symm

/-- `au_vis` for `AF` (= `⊤ AU`). -/
theorem af_vis {e : E.I} {k : E.O e → CTree E B X} (v : E.O e) :
    (entails ψ (CTree.vis e k) w ∨ NotDone w ∧ ∀ v, entails (AF ψ) (k v) (.obs e v)) ↔
      entails (AF ψ) (CTree.vis e k) w := by
  rw [← au_vis v, ticl_now, true_and]

end BasicLemmas

end Tisl
