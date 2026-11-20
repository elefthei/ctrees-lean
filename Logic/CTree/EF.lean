/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.EX

/-!
# The exists-until modality on ctrees

Structural rules for `φ EU ψ` on ctrees, the existential analogues of the `AU` rules: on a visible
event or branch one response or branch suffices (← `CTree/Logic/EF.v`).
-/

@[expose] public section
namespace Tisl
open CTree Notation
open ITree (Effect)

section BasicLemmas
variable {E B : Effect.{u}} {X : Type u} {i : Option (Type u)} {w : World E} {φ : TiclL E}
  {ψ : Ticl E i}

/-- A stuck tree satisfies `φ EU ψ` if and only if it satisfies `ψ`. -/
theorem eu_stuck :
    entails (φ EU ψ) (.stuck : CTree E B X) w ↔ entails ψ (.stuck : CTree E B X) w :=
  ⟨fun | .matchE h => h | .stepE _ _ _ tr _ => (ktrans_stuck tr).elim, .matchE⟩

/-- A return tree satisfies `φ EU ψ` if and only if it satisfies `ψ` or `φ EN ψ`. -/
theorem eu_ret {r : X} :
    entails (ψ ∨ₜ (φ EN ψ)) (pure r : CTree E B X) w ↔
      entails (φ EU ψ) (pure r : CTree E B X) w :=
  ⟨fun | .inl h => .matchE h | .inr h => (en_ret h).elim,
   fun | .matchE h => .inl h
       | .stepE t' w' hp tr h => (en_ret (φ := φ) (ψ := φ EU ψ) ⟨hp, t', w', tr, h⟩).elim⟩

/-- A hidden branch satisfies `φ EU ψ` if it satisfies `φ` and some successor of some branch
satisfies `φ EU ψ`. -/
theorem eu_br {c : B.I} {k : B.O c → CTree E B X} (hφ : entails φ (CTree.br c k) w)
    (hnext : ∃ y t' w', ktrans (k y) w t' w' ∧ entails (φ EU ψ) t' w') :
    entails (φ EU ψ) (CTree.br c k) w :=
  Euc.stepE' (en_br (ψ := φ EU ψ) |>.2 ⟨hφ, hnext⟩)

/-- A visible choice satisfies `φ EU ψ` if and only if it satisfies `ψ` or it satisfies `φ` and
some branch satisfies `φ EU ψ`. -/
theorem eu_brS {c : B.I} {k : B.O c → CTree E B X} :
    (entails ψ (CTree.brS c k) w ∨
      entails φ (CTree.brS c k) w ∧ ∃ y, entails (φ EU ψ) (k y) w) ↔
      entails (φ EU ψ) (CTree.brS c k) w :=
  (or_congr_right (en_brS (ψ := φ EU ψ)).symm).trans euc_unfold.symm

/-- A visible step satisfies `φ EU ψ` if and only if it satisfies `ψ` or it satisfies `φ` and its
continuation satisfies `φ EU ψ`. -/
theorem eu_step {t : CTree E B X} :
    (entails ψ (CTree.step t) w ∨ entails φ (CTree.step t) w ∧ entails (φ EU ψ) t w) ↔
      entails (φ EU ψ) (CTree.step t) w :=
  (or_congr_right (en_step (ψ := φ EU ψ)).symm).trans euc_unfold.symm

/-- A visible event satisfies `φ EU ψ` if and only if it satisfies `ψ` or it satisfies `φ` and
some response satisfies `φ EU ψ`. -/
theorem eu_vis {e : E.I} {k : E.O e → CTree E B X} :
    (entails ψ (CTree.vis e k) w ∨
      entails φ (CTree.vis e k) w ∧ ∃ v, entails (φ EU ψ) (k v) (.obs e v)) ↔
      entails (φ EU ψ) (CTree.vis e k) w :=
  (or_congr_right (en_vis (ψ := φ EU ψ)).symm).trans euc_unfold.symm

end BasicLemmas

end Tisl
