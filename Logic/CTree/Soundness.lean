/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Iter
public import Logic.Congruence

/-!
# Syntactic entailment and soundness

A single indexed derivation family `Syntails` shares prefix guards and indexed targets. Visible
branching has structural rules; hidden branching is handled only by transition-level semantic
lemmas, so some constructors carry semantic `entails` premises. `soundness` follows the derivation
(← `CTree/Logic/Soundness.v`).
-/

@[expose] public section
namespace Tisl
open CTree Notation
open ITree (Effect)

section SyntacticEntailment
variable {E B : Effect.{u}}

/-- Syntactic entailment (Rocq `syntails X b t w p`; the mode `b` is the formula index `i`). -/
inductive Syntails : {X : Type u} → {i : Option (Type u)} →
    CTree E B X → World E → Ticl E i → Prop
  -- Basic rules
  | synGuard {X i w} {φ : Ticl E i} {t : CTree E B X} :
      Syntails t w φ → Syntails (.guard t) w φ
  | synNow {X w} {φ : World E → Prop} {t : CTree E B X} :
      φ w → NotDone w → Syntails t w (.now φ)
  | synRet {X w} {R : X → World E → Prop} {x : X} :
      R x w → NotDone w → Syntails (pure x : CTree E B X) w (.ret R)
  | synAnd {X i} {t : CTree E B X} {w} {φ ψ : Ticl E i} :
      Syntails t w φ → Syntails t w ψ → Syntails t w (φ ∧ₜ ψ)
  | synOrL {X i} {t : CTree E B X} {w} {φ ψ : Ticl E i} :
      Syntails t w φ → Syntails t w (φ ∨ₜ ψ)
  | synOrR {X i} {t : CTree E B X} {w} {φ ψ : Ticl E i} :
      Syntails t w ψ → Syntails t w (φ ∨ₜ ψ)
  | synBindL {X Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {w} :
      Syntails t w φ → Syntails (t >>= k) w φ
  -- Universal until
  | synAuStuck {X i w} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (.stuck : CTree E B X) w ψ → Syntails (.stuck : CTree E B X) w (φ AU ψ)
  | synAuRetL {X i w} {φ : TiclL E} {ψ : Ticl E i} {r : X} :
      Syntails (pure r : CTree E B X) w ψ → Syntails (pure r : CTree E B X) w (φ AU ψ)
  | synAuRetR {X i w} {φ : TiclL E} {ψ : Ticl E i} {r : X} :
      Syntails (pure r : CTree E B X) w (φ AN ψ) → Syntails (pure r : CTree E B X) w (φ AU ψ)
  | synAuBrSR {X i w} {c : B.I} {k : B.O c → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.brS c k) w ψ → Syntails (CTree.brS c k) w (φ AU ψ)
  | synAuBrSL {X i w} {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) {φ : TiclL E}
      {ψ : Ticl E i} :
      Syntails (CTree.brS c k) w φ → (∀ y, Syntails (k y) w (φ AU ψ)) →
      Syntails (CTree.brS c k) w (φ AU ψ)
  | synAuStepR {X i w} {t : CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.step t) w ψ → Syntails (CTree.step t) w (φ AU ψ)
  | synAuStepL {X i w} {t : CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.step t) w φ → Syntails t w (φ AU ψ) → Syntails (CTree.step t) w (φ AU ψ)
  | synAuVisR {X i w} {e : E.I} {k : E.O e → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.vis e k) w ψ → Syntails (CTree.vis e k) w (φ AU ψ)
  | synAuVisL {X i w} {e : E.I} {k : E.O e → CTree E B X} (wit : E.O e) {φ : TiclL E}
      {ψ : Ticl E i} :
      Syntails (CTree.vis e k) w φ → (∀ v, Syntails (k v) (.obs e v) (φ AU ψ)) →
      Syntails (CTree.vis e k) w (φ AU ψ)
  | synAuBindR {X i Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} {w}
      (R : Y → World E → Prop) :
      entails (φ AU .ret R) t w → (∀ r w', R r w' → Syntails (k r) w' (φ AU ψ)) →
      Syntails (t >>= k) w (φ AU ψ)
  | synAuIterPrefix {X I : Type u} (Ri : I → World E → Prop)
      (Rv : I × World E → I × World E → Prop)
      {i : I} {w} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL E} :
      WellFounded Rv → NotDone w → Ri i w →
      (∀ i w, NotDone w → Ri i w →
        entails (φ AU ψ) (k i) w ∨
          entails (φ AU .ret fun (lr : I ⊕ X) w' =>
            ∃ i', lr = .inl i' ∧ NotDone w' ∧ Ri i' w' ∧ Rv (i', w') (i, w)) (k i) w) →
      Syntails (CTree.iter k i) w (φ AU ψ)
  | synAuIter {X I : Type u} {i} (Ri : I → World E → Prop)
      (Rv : I × World E → I × World E → Prop)
      {s : I} {w} {k : I → CTree E B (I ⊕ X)} {φ : TiclL E} {ψ : Ticl E i} :
      WellFounded Rv → Ri s w →
      (∀ s w, Ri s w →
        entails (φ AU .ret fun (lr : I ⊕ X) w' => match lr with
          | .inl s' => Ri s' w' ∧ Rv (s', w') (s, w)
          | .inr r => entails ψ (pure r : CTree E B X) w') (k s) w) →
      Syntails (CTree.iter k s) w (φ AU ψ)
  -- Existential until
  | synEuStuck {X i w} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (.stuck : CTree E B X) w ψ → Syntails (.stuck : CTree E B X) w (φ EU ψ)
  | synEuRetL {X i w} {φ : TiclL E} {ψ : Ticl E i} {r : X} :
      Syntails (pure r : CTree E B X) w ψ → Syntails (pure r : CTree E B X) w (φ EU ψ)
  | synEuRetR {X i w} {φ : TiclL E} {ψ : Ticl E i} {r : X} :
      Syntails (pure r : CTree E B X) w (φ EN ψ) → Syntails (pure r : CTree E B X) w (φ EU ψ)
  | synEuBrSR {X i w} {c : B.I} {k : B.O c → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.brS c k) w ψ → Syntails (CTree.brS c k) w (φ EU ψ)
  | synEuBrSL {X i w} {c : B.I} {k : B.O c → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.brS c k) w φ → (∃ y, entails (φ EU ψ) (k y) w) →
      Syntails (CTree.brS c k) w (φ EU ψ)
  | synEuStepR {X i w} {t : CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.step t) w ψ → Syntails (CTree.step t) w (φ EU ψ)
  | synEuStepL {X i w} {t : CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.step t) w φ → Syntails t w (φ EU ψ) → Syntails (CTree.step t) w (φ EU ψ)
  | synEuVisR {X i w} {e : E.I} {k : E.O e → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.vis e k) w ψ → Syntails (CTree.vis e k) w (φ EU ψ)
  | synEuVisL {X i w} {e : E.I} {k : E.O e → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.vis e k) w φ → (∃ v, entails (φ EU ψ) (k v) (.obs e v)) →
      Syntails (CTree.vis e k) w (φ EU ψ)
  | synEuBindR {X i Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} {w}
      (R : Y → World E → Prop) :
      entails (φ EU .ret R) t w → (∀ r w', R r w' → Syntails (k r) w' (φ EU ψ)) →
      Syntails (t >>= k) w (φ EU ψ)
  | synEuIterPrefix {X I : Type u} (Ri : I → World E → Prop)
      (Rv : I × World E → I × World E → Prop)
      {i : I} {w} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL E} :
      WellFounded Rv → NotDone w → Ri i w →
      (∀ i w, NotDone w → Ri i w →
        entails (φ EU ψ) (k i) w ∨
          entails (φ EU .ret fun (lr : I ⊕ X) w' =>
            ∃ i', lr = .inl i' ∧ NotDone w' ∧ Ri i' w' ∧ Rv (i', w') (i, w)) (k i) w) →
      Syntails (CTree.iter k i) w (φ EU ψ)
  | synEuIter {X I : Type u} {i} (Ri : I → World E → Prop)
      (Rv : I × World E → I × World E → Prop)
      {s : I} {w} {k : I → CTree E B (I ⊕ X)} {φ : TiclL E} {ψ : Ticl E i} :
      WellFounded Rv → Ri s w → NotDone w →
      (∀ s w, Ri s w → NotDone w →
        entails (φ EU .ret fun (lr : I ⊕ X) w' => match lr with
          | .inl s' => NotDone w' ∧ Ri s' w' ∧ Rv (s', w') (s, w)
          | .inr r => entails ψ (pure r : CTree E B X) w') (k s) w) →
      Syntails (CTree.iter k s) w (φ EU ψ)
  -- Universal next
  | synAnBrS {X i w} {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) {φ : TiclL E}
      {ψ : Ticl E i} :
      Syntails (CTree.brS c k) w φ → (∀ y, Syntails (k y) w ψ) →
      Syntails (CTree.brS c k) w (φ AN ψ)
  | synAnStep {X i w} {t : CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.step t) w φ → Syntails t w ψ → Syntails (CTree.step t) w (φ AN ψ)
  | synAnVis {X i w} {e : E.I} {k : E.O e → CTree E B X} (wit : E.O e) {φ : TiclL E}
      {ψ : Ticl E i} :
      Syntails (CTree.vis e k) w φ → (∀ v, Syntails (k v) (.obs e v) ψ) →
      Syntails (CTree.vis e k) w (φ AN ψ)
  | synAnBindL {X i Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} {w}
      (R : Y → World E → Prop) :
      entails (φ AN .ret R) t w → (∀ r w', R r w' → Syntails (k r) w' ψ) →
      Syntails (t >>= k) w (φ AN ψ)
  | synAnBindR {X i Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} {w}
      (R : Y → World E → Prop) :
      entails (.ret R) t w → (∀ r w', R r w' → Syntails (k r) w' (φ AN ψ)) →
      Syntails (t >>= k) w (φ AN ψ)
  | synAnIter {X I : Type u} (Ri : I → World E → Prop) (Rv : I → I → Prop) {i : I} {w}
      {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL E} :
      WellFounded Rv → Ri i w →
      (∀ i w, Ri i w →
        entails (φ AN ψ) (k i) w ∨
          entails (.ret fun (lr : I ⊕ X) w' => ∃ i', lr = .inl i' ∧ Ri i' w' ∧ Rv i' i) (k i) w) →
      Syntails (CTree.iter k i) w (φ AN ψ)
  -- Existential next
  | synEnBrS {X i w} {c : B.I} {k : B.O c → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.brS c k) w φ → (∃ y, entails ψ (k y) w) →
      Syntails (CTree.brS c k) w (φ EN ψ)
  | synEnStep {X i w} {t : CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.step t) w φ → Syntails t w ψ → Syntails (CTree.step t) w (φ EN ψ)
  | synEnVis {X i w} {e : E.I} {k : E.O e → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} :
      Syntails (CTree.vis e k) w φ → (∃ v, entails ψ (k v) (.obs e v)) →
      Syntails (CTree.vis e k) w (φ EN ψ)
  | synEnBindR {X i Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {ψ : Ticl E i} {w}
      (R : Y → World E → Prop) :
      entails (.ret R) t w → (∀ r w', R r w' → Syntails (k r) w' (φ EN ψ)) →
      Syntails (t >>= k) w (φ EN ψ)
  | synEnIter {X I : Type u} (Ri : I → World E → Prop) (Rv : I → I → Prop) {i : I} {w}
      {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL E} :
      WellFounded Rv → Ri i w →
      (∀ i w, Ri i w →
        entails (φ EN ψ) (k i) w ∨
          entails (.ret fun (lr : I ⊕ X) w' => ∃ i', lr = .inl i' ∧ Ri i' w' ∧ Rv i' i) (k i) w) →
      Syntails (CTree.iter k i) w (φ EN ψ)
  -- Always
  | synAgBrS {X w} {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) {φ : TiclL E} :
      Syntails (CTree.brS c k) w φ → (∀ y, Syntails (k y) w (AG φ)) →
      Syntails (CTree.brS c k) w (AG φ)
  | synAgStep {X w} {t : CTree E B X} {φ : TiclL E} :
      Syntails (CTree.step t) w φ → Syntails t w (AG φ) → Syntails (CTree.step t) w (AG φ)
  | synAgVis {X w} {e : E.I} {k : E.O e → CTree E B X} (wit : E.O e) {φ : TiclL E} :
      Syntails (CTree.vis e k) w φ → (∀ v, Syntails (k v) (.obs e v) (AG φ)) →
      Syntails (CTree.vis e k) w (AG φ)
  | synAgBindR {X Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {w}
      (R : Y → World E → Prop) :
      entails (φ AU .ret R) t w → (∀ r w', R r w' → Syntails (k r) w' (AG φ)) →
      Syntails (t >>= k) w (AG φ)
  | synAgIter {X I : Type u} (R : I → World E → Prop) {i : I} {w}
      {k : I → CTree E B (I ⊕ X)} {φ : TiclL E} :
      R i w →
      (∀ i w, R i w →
        entails φ (CTree.iter k i) w ∧
          entails (AX (φ AU .ret fun (lr : I ⊕ X) w' => ∃ i', lr = .inl i' ∧ R i' w')) (k i) w) →
      Syntails (CTree.iter k i) w (AG φ)
  -- Existential always
  | synEgBrS {X w} {c : B.I} {k : B.O c → CTree E B X} {φ : TiclL E} :
      Syntails (CTree.brS c k) w φ → (∃ y, entails (EG φ) (k y) w) →
      Syntails (CTree.brS c k) w (EG φ)
  | synEgStep {X w} {t : CTree E B X} {φ : TiclL E} :
      Syntails (CTree.step t) w φ → Syntails t w (EG φ) → Syntails (CTree.step t) w (EG φ)
  | synEgVis {X w} {e : E.I} {k : E.O e → CTree E B X} {φ : TiclL E} :
      Syntails (CTree.vis e k) w φ → (∃ v, entails (EG φ) (k v) (.obs e v)) →
      Syntails (CTree.vis e k) w (EG φ)
  | synEgBindR {X Y} {t : CTree E B Y} {k : Y → CTree E B X} {φ : TiclL E} {w}
      (R : Y → World E → Prop) :
      entails (φ EU .ret R) t w → (∀ r w', R r w' → Syntails (k r) w' (EG φ)) →
      Syntails (t >>= k) w (EG φ)
  | synEgIter {X I : Type u} (R : I → World E → Prop) {i : I} {w}
      {k : I → CTree E B (I ⊕ X)} {φ : TiclL E} :
      R i w →
      (∀ i w, R i w →
        entails φ (CTree.iter k i) w ∧
          entails (EX (φ EU .ret fun (lr : I ⊕ X) w' => ∃ i', lr = .inl i' ∧ R i' w')) (k i) w) →
      Syntails (CTree.iter k i) w (EG φ)

/-- Soundness follows the derivation, including its prefix-guard evidence. -/
theorem soundness {X : Type u} {i : Option (Type u)} {t : CTree E B X} {w : World E}
    {p : Ticl E i} (h : Syntails t w p) : entails p t w := by
  induction h with
  | synGuard _ ih => exact (proper_entails_meq _ (sb_guard _)).2 ih
  | synNow hφ hd => exact ⟨hφ, hd⟩
  | synRet hR hd => exact ret_ret hd hR
  | synAnd _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | synOrL _ ih => exact .inl ih
  | synOrR _ ih => exact .inr ih
  | synBindL _ ih => exact ticll_bind_l ih
  | synAuStuck _ ih => exact au_stuck.1 ih
  | synAuRetL _ ih => exact au_ret.1 (.inl ih)
  | synAuRetR _ ih => exact au_ret.1 (.inr ih)
  | synAuBrSR _ ih => exact .matchA ih
  | synAuBrSL y _ _ ih₁ ih₂ => exact (au_brS y).1 (.inr ⟨ih₁, ih₂⟩)
  | synAuStepR _ ih => exact .matchA ih
  | synAuStepL _ _ ih₁ ih₂ => exact au_step.1 (.inr ⟨ih₁, ih₂⟩)
  | synAuVisR _ ih => exact .matchA ih
  | synAuVisL wit _ _ ih₁ ih₂ => exact (au_vis wit).1 (.inr ⟨ih₁, ih₂⟩)
  | synAuBindR R h _ ih => exact u_bind_r h ih
  | synAuIterPrefix Ri Rv hwf hd hi hbody => exact u_iter_prefix Ri Rv hwf hd hi hbody
  | synAuIter Ri Rv hwf hi hbody => exact u_iter Ri Rv hwf hi hbody
  | synEuStuck _ ih => exact eu_stuck.2 ih
  | synEuRetL _ ih => exact eu_ret.1 (.inl ih)
  | synEuRetR _ ih => exact eu_ret.1 (.inr ih)
  | synEuBrSR _ ih => exact .matchE ih
  | synEuBrSL _ h ih => exact eu_brS.1 (.inr ⟨ih, h⟩)
  | synEuStepR _ ih => exact .matchE ih
  | synEuStepL _ _ ih₁ ih₂ => exact eu_step.1 (.inr ⟨ih₁, ih₂⟩)
  | synEuVisR _ ih => exact .matchE ih
  | synEuVisL _ h ih => exact eu_vis.1 (.inr ⟨ih, h⟩)
  | synEuBindR R h _ ih => exact u_bind_r h ih
  | synEuIterPrefix Ri Rv hwf hd hi hbody => exact u_iter_prefix Ri Rv hwf hd hi hbody
  | @synEuIter _ _ _ Ri Rv _ _ _ φ _ hwf hi hd hbody =>
    exact u_iter (fun s w => NotDone w ∧ Ri s w) Rv hwf ⟨hd, hi⟩ fun s z ⟨hd, hi⟩ =>
      impl_ticl_until .E (impl_ticl_refl φ) (ret_impl_ticl _ _ fun
        | .inl _, _, ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩
        | .inr _, _, h => h) _ _ (hbody s z hi hd)
  | synAnBrS y _ _ ih₁ ih₂ => exact (an_brS y).2 ⟨ih₁, ih₂⟩
  | synAnStep _ _ ih₁ ih₂ => exact an_step.2 ⟨ih₁, ih₂⟩
  | synAnVis wit _ _ ih₁ ih₂ => exact (an_vis wit).2 ⟨ih₁, ih₂⟩
  | synAnBindL R h _ ih => exact an_bind_l h ih
  | synAnBindR R h _ ih => exact ticl_bind_ret h ih
  | synAnIter Ri Rv hwf hi H => exact n_iter_prefix Ri Rv hwf hi H
  | synEnBrS _ h ih => exact en_brS.2 ⟨ih, h⟩
  | synEnStep _ _ ih₁ ih₂ => exact en_step.2 ⟨ih₁, ih₂⟩
  | synEnVis _ h ih => exact en_vis.2 ⟨ih, h⟩
  | synEnBindR R h _ ih => exact ticl_bind_ret h ih
  | synEnIter Ri Rv hwf hi H => exact n_iter_prefix Ri Rv hwf hi H
  | synAgBrS y _ _ ih₁ ih₂ => exact (ag_brS y).1 ⟨ih₁, ih₂⟩
  | synAgStep _ _ ih₁ ih₂ => exact ag_step.1 ⟨ih₁, ih₂⟩
  | synAgVis wit _ _ ih₁ ih₂ => exact (ag_vis wit).1 ⟨ih₁, ih₂⟩
  | synAgBindR R h _ ih => exact ag_bind_r h ih
  | synAgIter R hR H => exact ag_iter R hR H
  | synEgBrS _ h ih => exact eg_brS.1 ⟨ih, h⟩
  | synEgStep _ _ ih₁ ih₂ => exact eg_step.1 ⟨ih₁, ih₂⟩
  | synEgVis _ h ih => exact eg_vis.1 ⟨ih, h⟩
  | synEgBindR R h _ ih => exact eg_bind_r h ih
  | synEgIter R hR H => exact eg_iter R hR H

end SyntacticEntailment

end Tisl
