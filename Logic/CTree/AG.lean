/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.AX

/-!
# Forall-always on ctrees

Structural rules for the forall-always modality `AG φ` on ctrees, by the head constructor of the
tree; silently diverging trees satisfy no `AG` formula (← `CTree/Logic/AG.v`).
-/

@[expose] public section
namespace Tisl
open CTree Notation
open ITree (Effect)

section BasicLemmas
variable {E B : Effect.{u}} {X : Type u} {w : World E} {φ : TiclL E}

/-- Vis iff lemma for forall-always. -/
theorem ag_vis {e : E.I} {k : E.O e → CTree E B X} (v : E.O e) :
    (entails φ (CTree.vis e k) w ∧ ∀ v, entails (AG φ) (k v) (.obs e v)) ↔
      entails (AG φ) (CTree.vis e k) w :=
  (agc_unfold.trans (an_vis (φ := φ) (ψ := AG φ) v)).symm

/-- Visible branch iff lemma for forall-always. -/
theorem ag_brS {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) :
    (entails φ (CTree.brS c k) w ∧ ∀ y, entails (AG φ) (k y) w) ↔
      entails (AG φ) (CTree.brS c k) w :=
  (agc_unfold.trans (an_brS (φ := φ) (ψ := AG φ) y)).symm

/-- Visible step iff lemma for forall-always. -/
theorem ag_step {t : CTree E B X} :
    (entails φ (CTree.step t) w ∧ entails (AG φ) t w) ↔ entails (AG φ) (CTree.step t) w :=
  (agc_unfold.trans (an_step (φ := φ) (ψ := AG φ))).symm

/-- Hidden branch lemma for forall-always: all successors of all branches satisfy `AG φ` and at
least one branch can step. -/
theorem ag_br {c : B.I} {k : B.O c → CTree E B X} (hφ : entails φ (CTree.br c k) w)
    (hs : ∃ y, can_step (k y) w)
    (hk : ∀ y t' w', ktrans (k y) w t' w' → entails (AG φ) t' w') :
    entails (AG φ) (CTree.br c k) w :=
  agc_unfold.2 (an_br (ψ := AG φ) hφ hs hk)

/-- A stuck tree does not step, so it satisfies no `AG` formula. -/
theorem ag_stuck : ¬ entails (AG φ) (CTree.stuck : CTree E B X) w :=
  fun h => an_stuck (φ := φ) (ψ := AG φ) (agc_unfold.1 h)

/-- A returning tree does not step forever, so it satisfies no `AG` formula. -/
theorem ag_ret {x : X} : ¬ entails (AG φ) (pure x : CTree E B X) w :=
  fun h => an_ret (φ := φ) (ψ := AG φ) (agc_unfold.1 h)

end BasicLemmas

/-- Silent divergence has no productive global derivation. -/
theorem guard_fixed_no_ag {E B : Effect.{u}} {X : Type u} (t : CTree E B X) (w : World E)
    (φ : TiclL E) (ht : t = .guard t) : ¬ entails (AG φ) t w := fun h => by
  obtain ⟨t', w', tr⟩ := (agc_unfold.1 h).2.1
  obtain ⟨l, tr, -⟩ := ktrans_trans.1 tr
  rw [guard_fixed_spin t ht] at tr
  exact spin_isStuck _ _ tr

end Tisl
