/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.EX
public import Logic.Utils.Execution
public import Logic.Utils.Relations

/-!
# The exists-always modality on ctrees

Structural rules for `EG φ` on ctrees: the current guard plus one continuing successor; stuck trees
and returns cannot satisfy it. `egc_of_sequence` builds `egc` from a productive sequence of
transitions (← `CTree/Logic/EG.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinduction Notation
open ITree (Effect)

section BasicLemmas
variable {E B : Effect.{u}} {X : Type u} {w : World E} {φ : TiclL E}

/-- A visible event satisfies `EG φ` iff it satisfies `φ` and its continuation `k v` satisfies
`EG φ` for some `v`. -/
theorem eg_vis {e : E.I} {k : E.O e → CTree E B X} :
    (entails φ (CTree.vis e k) w ∧ ∃ v, entails (EG φ) (k v) (.obs e v)) ↔
      entails (EG φ) (CTree.vis e k) w :=
  (en_vis (ψ := EG φ)).symm.trans (egc_unfold (p := entails φ)).symm

/-- A visible branch satisfies `EG φ` iff it satisfies `φ` and its continuation `k y` satisfies
`EG φ` for some `y`. -/
theorem eg_brS {c : B.I} {k : B.O c → CTree E B X} :
    (entails φ (CTree.brS c k) w ∧ ∃ y, entails (EG φ) (k y) w) ↔
      entails (EG φ) (CTree.brS c k) w :=
  (en_brS (ψ := EG φ)).symm.trans (egc_unfold (p := entails φ)).symm

/-- A visible step satisfies `EG φ` iff it satisfies `φ` and its continuation satisfies `EG φ`. -/
theorem eg_step {t : CTree E B X} :
    (entails φ (CTree.step t) w ∧ entails (EG φ) t w) ↔ entails (EG φ) (CTree.step t) w :=
  (en_step (ψ := EG φ)).symm.trans (egc_unfold (p := entails φ)).symm

/-- A hidden branch satisfies `EG φ` if it satisfies `φ` and some branch has a successor
satisfying `EG φ`. -/
theorem eg_br {c : B.I} {k : B.O c → CTree E B X} (hφ : entails φ (CTree.br c k) w)
    (hnext : ∃ y t' w', ktrans (k y) w t' w' ∧ entails (EG φ) t' w') :
    entails (EG φ) (CTree.br c k) w :=
  egc_unfold.2 (en_br (ψ := EG φ) |>.2 ⟨hφ, hnext⟩)

/-- Inversion of `EG φ` at a hidden branch: some branch has a successor satisfying `EG φ`. -/
theorem eg_br_inv {c : B.I} {k : B.O c → CTree E B X} (h : entails (EG φ) (CTree.br c k) w) :
    entails φ (CTree.br c k) w ∧ ∃ y t' w', ktrans (k y) w t' w' ∧ entails (EG φ) t' w' :=
  en_br (ψ := EG φ) |>.1 (egc_unfold.1 h)

/-- A stuck tree does not satisfy `EG φ`; it does not step. -/
theorem eg_stuck : ¬ entails (EG φ) (.stuck : CTree E B X) w :=
  fun h => let ⟨_, _, _, tr, _⟩ := egc_unfold.1 h; ktrans_stuck tr

/-- A return tree does not satisfy `EG φ`; it does not infinitely step. -/
theorem eg_ret {x : X} : ¬ entails (EG φ) (pure x : CTree E B X) w := by
  intro h
  obtain ⟨hφ, t', w', tr, h⟩ := egc_unfold.1 h
  cases ticl_not_done φ hφ
  · obtain ⟨rfl, rfl⟩ := ktrans_done.1 tr; exact eg_stuck (φ := φ) h
  · obtain ⟨rfl, rfl⟩ := ktrans_finish.1 tr; exact eg_stuck (φ := φ) h

end BasicLemmas

/-- A productive sequence of raw transitions establishes existential always. Indices without a
retained transition preserve both the tree and world. -/
theorem egc_of_sequence {E B : Effect.{u}} {X : Type u}
    (T : Nat → CTree E B X) (W : Nat → World E) (V : Nat → Prop)
    (P : CTree E B X → World E → Prop) (Hdec : ∀ n, Decidable (V n)) (Hinf : infinitely V)
    (HP : ∀ n, P (T n) (W n)) (Hproper : SbProper P)
    (Hskip : ∀ n, ¬ V n → T n ~ T (n + 1) ∧ W (n + 1) = W n)
    (Hstep : ∀ n, V n → ∃ u, ktrans (T n) (W n) u (W (n + 1)) ∧ u ~ T (n + 1)) :
    ∀ n, egc P (T n) (W n) := by
  have Hinterval : ∀ n len, (∀ j, n ≤ j ∧ j < n + len → ¬ V j) →
      T n ~ T (n + len) ∧ W (n + len) = W n := by
    intro n len
    induction len with
    | zero => intro; exact ⟨sbisim_refl _, rfl⟩
    | succ len ih =>
      intro hnone
      have ⟨Et, Ew⟩ := ih fun j hj => hnone j ⟨hj.1, by omega⟩
      have ⟨Et', Ew'⟩ := Hskip (n + len) (hnone _ ⟨by omega, by omega⟩)
      exact ⟨sbisim_trans Et Et', Ew'.trans Ew⟩
  let Z : CTree E B X → World E → Prop := fun t w => ∃ n, t ~ T n ∧ w = W n
  have HZ : ∀ t w, Z t w → egcF P Z t w := by
    rintro t w ⟨n, Et, rfl⟩
    refine ⟨(Hproper _ Et).2 (HP n), ?_⟩
    obtain ⟨bound, hbound, HV⟩ := Hinf n
    rcases finite_first V Hdec n (bound + 1 - n) with hnone | ⟨m, hm, hvisible, hfirst⟩
    · exact (hnone bound ⟨hbound, by omega⟩ HV).elim
    · have ⟨Eprefix, Eworld⟩ := Hinterval n (m - n) fun j hj => hfirst j ⟨hj.1, by omega⟩
      rw [show n + (m - n) = m by omega] at Eprefix Eworld
      obtain ⟨u, hu, Eu⟩ := Hstep m hvisible
      rw [Eworld] at hu
      obtain ⟨v, hv, Euv⟩ := ktrans_semiproper (sbisim_symm (sbisim_trans Et Eprefix)) hu
      exact ⟨v, W (m + 1), hv, m + 1, sbisim_trans (sbisim_symm Euv) Eu, rfl⟩
  exact fun n => le_gfp (b := egcF P) (x := Z) HZ _ _ ⟨n, sbisim_refl _, rfl⟩

end Tisl
