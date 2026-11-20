/- SPDX-License-Identifier: MIT -/
module

public import Logic.Semantics

/-!
# Congruences of TICL

Semantic implication `impl_ticl M B X p q` and equivalence `equiv_ticl M B X p q` of formulas at a
fixed model type `M E B X`, their congruence laws for every connective, and the standard equations
of the until/always modalities (← `Logic/Congruence.v`). The model family `M` and branch effect
`B` are explicit arguments: they cannot be inferred from the formulas.
-/

@[expose] public section
namespace Tisl
open ITree (Effect)
open CTree.Coinduction Notation

/-- Semantic implication at a model type (Rocq `impl_ticl X b`). -/
def impl_ticl (M : Effect.{u} → Effect.{u} → Type u → Type u) {E : Effect.{u}} (B : Effect.{u})
    [Kripke M E B] (X : Type u) {i : Option (Type u)} (p q : Ticl E i) : Prop :=
  ∀ (t : M E B X) w, entails p t w → entails q t w

/-- Semantic equivalence at a model type (Rocq `equiv_ticl X b`). -/
def equiv_ticl (M : Effect.{u} → Effect.{u} → Type u → Type u) {E : Effect.{u}} (B : Effect.{u})
    [Kripke M E B] (X : Type u) {i : Option (Type u)} (p q : Ticl E i) : Prop :=
  impl_ticl M B X p q ∧ impl_ticl M B X q p

/-- Implication of prefix formulas (Rocq notation `⋖L`). -/
abbrev impl_ticll (M : Effect.{u} → Effect.{u} → Type u → Type u) {E : Effect.{u}}
    (B : Effect.{u}) [Kripke M E B] (X : Type u) (p q : TiclL E) : Prop := impl_ticl M B X p q
/-- Implication of return formulas (Rocq notation `⋖R`). -/
abbrev impl_ticlr (M : Effect.{u} → Effect.{u} → Type u → Type u) {E : Effect.{u}}
    (B : Effect.{u}) [Kripke M E B] (X : Type u) (p q : TiclR E X) : Prop := impl_ticl M B X p q
/-- Equivalence of prefix formulas (Rocq notation `⩸L`). -/
abbrev equiv_ticll (M : Effect.{u} → Effect.{u} → Type u → Type u) {E : Effect.{u}}
    (B : Effect.{u}) [Kripke M E B] (X : Type u) (p q : TiclL E) : Prop := equiv_ticl M B X p q
/-- Equivalence of return formulas (Rocq notation `⩸R`). -/
abbrev equiv_ticlr (M : Effect.{u} → Effect.{u} → Type u → Type u) {E : Effect.{u}}
    (B : Effect.{u}) [Kripke M E B] (X : Type u) (p q : TiclR E X) : Prop := equiv_ticl M B X p q

variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {E B : Effect.{u}} [Kripke M E B]
  {X : Type u} {i : Option (Type u)}

set_option hygiene false in
local infix:58 " ⋖ " => impl_ticl M B X
set_option hygiene false in
local infix:58 " ⩸ " => equiv_ticl M B X

/-! ## Preorder and equivalence -/

theorem impl_ticl_refl (p : Ticl E i) : p ⋖ p := fun _ _ h => h

theorem impl_ticl_trans {p q r : Ticl E i} (hpq : p ⋖ q) (hqr : q ⋖ r) : p ⋖ r :=
  fun t w h => hqr t w (hpq t w h)

theorem equiv_ticl_equivalence : Equivalence (equiv_ticl M B X (E := E) (i := i)) where
  refl p := ⟨impl_ticl_refl p, impl_ticl_refl p⟩
  symm h := ⟨h.2, h.1⟩
  trans h h' := ⟨impl_ticl_trans h.1 h'.1, impl_ticl_trans h'.2 h.2⟩

theorem equiv_ticl_impl {p q p' q' : Ticl E i} (h : p ⩸ q) (h' : p' ⩸ q') :
    (p ⋖ p') ↔ (q ⋖ q') :=
  ⟨fun hp => impl_ticl_trans h.2 (impl_ticl_trans hp h'.1),
   fun hq => impl_ticl_trans h.1 (impl_ticl_trans hq h'.2)⟩

theorem equiv_ticl_equiv {p q p' q' : Ticl E i} (h : p ⩸ q) (h' : p' ⩸ q') :
    (p ⩸ p') ↔ (q ⩸ q') :=
  ⟨fun hp => ⟨(equiv_ticl_impl h h').1 hp.1, (equiv_ticl_impl h' h).1 hp.2⟩,
   fun hq => ⟨(equiv_ticl_impl h h').2 hq.1, (equiv_ticl_impl h' h).2 hq.2⟩⟩

/-! ## Congruence of the connectives -/

theorem impl_ticl_entails {p q : Ticl E i} (h : p ⋖ q) {t : M E B X} {w : World E} :
    entails p t w → entails q t w := h t w

theorem equiv_ticl_entails {p q : Ticl E i} (h : p ⩸ q) {t : M E B X} {w : World E} :
    entails p t w ↔ entails q t w := ⟨h.1 t w, h.2 t w⟩

theorem impl_ticl_and {p q p' q' : Ticl E i} (h : p ⋖ q) (h' : p' ⋖ q') :
    (p ∧ₜ p') ⋖ (q ∧ₜ q') := fun t w H => ⟨h t w H.1, h' t w H.2⟩

theorem equiv_ticl_and {p q p' q' : Ticl E i} (h : p ⩸ q) (h' : p' ⩸ q') :
    (p ∧ₜ p') ⩸ (q ∧ₜ q') := ⟨impl_ticl_and h.1 h'.1, impl_ticl_and h.2 h'.2⟩

theorem impl_ticl_or {p q p' q' : Ticl E i} (h : p ⋖ q) (h' : p' ⋖ q') :
    (p ∨ₜ p') ⋖ (q ∨ₜ q') := fun t w H => H.imp (h t w) (h' t w)

theorem equiv_ticl_or {p q p' q' : Ticl E i} (h : p ⩸ q) (h' : p' ⩸ q') :
    (p ∨ₜ p') ⩸ (q ∨ₜ q') := ⟨impl_ticl_or h.1 h'.1, impl_ticl_or h.2 h'.2⟩

theorem impl_ticl_next (c : Ticlq) {p q : TiclL E} {p' q' : Ticl E i} (h : p ⋖ q)
    (h' : p' ⋖ q') : Ticl.cx c p p' ⋖ Ticl.cx c q q' := by
  cases c
  · exact fun t w ⟨hp, hs, hk⟩ => ⟨h t w hp, hs, fun t' w' tr => h' t' w' (hk t' w' tr)⟩
  · exact fun t w ⟨hp, t', w', tr, hr⟩ => ⟨h t w hp, t', w', tr, h' t' w' hr⟩

theorem equiv_ticl_next (c : Ticlq) {p q : TiclL E} {p' q' : Ticl E i} (h : p ⩸ q)
    (h' : p' ⩸ q') : Ticl.cx c p p' ⩸ Ticl.cx c q q' :=
  ⟨impl_ticl_next c h.1 h'.1, impl_ticl_next c h.2 h'.2⟩

theorem impl_ticl_until (c : Ticlq) {p q : TiclL E} {p' q' : Ticl E i} (h : p ⋖ q)
    (h' : p' ⋖ q') : Ticl.cu c p p' ⋖ Ticl.cu c q q' := by
  cases c
  · exact fun t w H => auc_mono_r (fun t w => h' t w) t w (auc_mono_l (fun t w => h t w) t w H)
  · exact fun t w H => euc_mono_r (fun t w => h' t w) t w (euc_mono_l (fun t w => h t w) t w H)

theorem equiv_ticl_until (c : Ticlq) {p q : TiclL E} {p' q' : Ticl E i} (h : p ⩸ q)
    (h' : p' ⩸ q') : Ticl.cu c p p' ⩸ Ticl.cu c q q' :=
  ⟨impl_ticl_until c h.1 h'.1, impl_ticl_until c h.2 h'.2⟩

theorem impl_ticl_global (c : Ticlq) {p q : TiclL E} (h : p ⋖ q) : Ticl.cg c p ⋖ Ticl.cg c q := by
  cases c
  · exact gfp_mono (b := agcF (entails p)) (c := agcF (entails q))
      fun _ t w ⟨hp, hs, hk⟩ => ⟨h t w hp, hs, hk⟩
  · exact gfp_mono (b := egcF (entails p)) (c := egcF (entails q))
      fun _ t w ⟨hp, hr⟩ => ⟨h t w hp, hr⟩

theorem equiv_ticl_global (c : Ticlq) {p q : TiclL E} (h : p ⩸ q) :
    Ticl.cg c p ⩸ Ticl.cg c q :=
  ⟨impl_ticl_global c h.1, impl_ticl_global c h.2⟩

theorem ret_impl_ticl (P Q : X → World E → Prop) (hPQ : ∀ x w, P x w → Q x w) :
    Ticl.ret P ⋖ Ticl.ret Q :=
  fun _ _ ⟨x, hp, h⟩ => ⟨x, hPQ x _ hp, h⟩

theorem aur_ret_mono (t : M E B X) (w : World E) (φ : TiclL E) (P Q : X → World E → Prop)
    (hPQ : ∀ x w, P x w → Q x w) (h : entails (φ AU .ret P) t w) :
    entails (φ AU .ret Q) t w :=
  impl_ticl_until .A (impl_ticl_refl φ) (ret_impl_ticl P Q hPQ) t w h

theorem aur_done_mono (t : M E B X) (w : World E) (φ : TiclL E) (P Q : X → World E → Prop)
    (hPQ : ∀ x w, P x w → Q x w) (h : Auc (entails φ) (fun _ wd => DoneWith P wd) t w) :
    Auc (entails φ) (fun _ wd => DoneWith Q wd) t w :=
  auc_mono_r (fun _ _ hd => done_with_mono hPQ hd) t w h

/-! ## Equations of formulas at any index -/

section TiclEquations
variable (p q r : Ticl E i)

/-- Left injection of `p` into `p ∨ q`. -/
theorem impl_or_injL : p ⋖ (p ∨ₜ q) := fun _ _ => .inl

/-- Right injection of `q` into `p ∨ q`. -/
theorem impl_or_injR : q ⋖ (p ∨ₜ q) := fun _ _ => .inr

theorem impl_or_impl_or (h : (p ∨ₜ q) ⋖ r) : (p ⋖ r) ∨ (q ⋖ r) :=
  .inl fun t w hp => h t w (.inl hp)

theorem impl_or_impl_and (h : (p ⋖ r) ∧ (q ⋖ r)) : (p ∨ₜ q) ⋖ r :=
  fun t w H => H.elim (h.1 t w) (h.2 t w)

/-- `(p AN q) ∨ (p AN r)` implies `p AN (q ∨ r)` (the converse loses which branch holds). -/
theorem impl_an_or (p : TiclL E) (q r : Ticl E i) :
    ((p AN q) ∨ₜ (p AN r)) ⋖ (p AN (q ∨ₜ r)) :=
  impl_or_impl_and _ _ _
    ⟨impl_ticl_next .A (impl_ticl_refl p) (impl_or_injL q r),
     impl_ticl_next .A (impl_ticl_refl p) (impl_or_injR q r)⟩

/-- `p AU q` is `q` or `p` now and `p AU q` next. -/
theorem equiv_au_an (p : TiclL E) (q : Ticl E i) : (p AU q) ⩸ (q ∨ₜ (p AN (p AU q))) :=
  ⟨fun _ _ h => auc_unfold.1 h, fun _ _ h => auc_unfold.2 h⟩

/-- `p EU q` is `q` or `p` now and `p EU q` next. -/
theorem equiv_eu_en (p : TiclL E) (q : Ticl E i) : (p EU q) ⩸ (q ∨ₜ (p EN (p EU q))) :=
  ⟨fun _ _ h => euc_unfold.1 h, fun _ _ h => euc_unfold.2 h⟩

/-- `p AU (p AN q)` implies `p AN (p AU q)`. -/
theorem impl_auan_anau (p : TiclL E) (q : Ticl E i) : (p AU (p AN q)) ⋖ (p AN (p AU q)) := by
  intro t w (h : Auc _ _ t w)
  induction h with
  | matchA h => exact anc_mono_r (fun _ _ => .matchA) _ _ h
  | stepA hp hs _ ih => exact ⟨hp, hs, fun t' w' tr => Auc.stepA' (ih t' w' tr)⟩

/-- `p EU (p EN q)` implies `p EN (p EU q)`. -/
theorem impl_euen_eneu (p : TiclL E) (q : Ticl E i) : (p EU (p EN q)) ⋖ (p EN (p EU q)) := by
  intro t w (h : Euc _ _ t w)
  induction h with
  | matchE h => exact enc_mono_r (fun _ _ => .matchE) _ _ h
  | stepE t' w' hp tr _ ih => exact ⟨hp, t', w', tr, Euc.stepE' ih⟩

/-- `p AU q` is idempotent. -/
theorem equiv_au_idem (p : TiclL E) (q : Ticl E i) : (p AU q) ⩸ (p AU (p AU q)) :=
  ⟨fun _ _ => .matchA, fun t w => auc_join t w⟩

/-- `p EU q` is idempotent. -/
theorem equiv_eu_idem (p : TiclL E) (q : Ticl E i) : (p EU q) ⩸ (p EU (p EU q)) :=
  ⟨fun _ _ => .matchE, fun t w => euc_join t w⟩

end TiclEquations

/-! ## Equations of prefix formulas -/

section TicllEquations
variable (p q : TiclL E)

/-- Unfold a `vis` formula into a `now` formula. -/
theorem equivl_vis_now (φ : (e : E.I) → E.O e → Prop) :
    (visₜ φ) ⩸ Ticl.now fun w => ∃ e v, w = .obs e v ∧ φ e v :=
  ⟨fun _ _ ⟨hv, hd⟩ => by cases hv with | obs e v h => exact ⟨⟨e, v, rfl, h⟩, hd⟩,
   fun _ _ ⟨⟨e, v, hw, h⟩, hd⟩ => ⟨hw ▸ .obs e v h, hd⟩⟩

/-- `⊤` is a left identity of `∧`. -/
theorem equivl_and_idL : (⊤ ∧ₜ p) ⩸ p :=
  ⟨fun _ _ h => h.2, fun _ _ h => ⟨⟨trivial, ticl_not_done p h⟩, h⟩⟩

/-- `⊤` is a right identity of `∧`. -/
theorem equivl_and_idR : (p ∧ₜ ⊤) ⩸ p :=
  ⟨fun _ _ h => h.1, fun _ _ h => ⟨h, trivial, ticl_not_done p h⟩⟩

/-- `⊥` is a left identity of `∨`. -/
theorem equivl_or_idL : (⊥ ∨ₜ p) ⩸ p :=
  ⟨fun _ _ h => h.elim (fun h => (ticll_sound h).elim) id, fun _ _ => .inr⟩

/-- `⊥` is a right identity of `∨`. -/
theorem equivl_or_idR : (p ∨ₜ ⊥) ⩸ p :=
  ⟨fun _ _ h => h.elim id fun h => (ticll_sound h).elim, fun _ _ => .inl⟩

/-- `AG p` is `p` now and `AG p` after every step. -/
theorem equivl_ag_an : (AG p) ⩸ (p AN (AG p)) :=
  ⟨fun _ _ h => agc_unfold.1 h, fun _ _ h => agc_unfold.2 h⟩

/-- `EG p` is `p` now and `EG p` after some step. -/
theorem equivl_eg_en : (EG p) ⩸ (p EN (EG p)) :=
  ⟨fun _ _ h => egc_unfold.1 h, fun _ _ h => egc_unfold.2 h⟩

theorem impll_ag_refl : (AG p) ⋖ p := fun _ _ h => (agc_unfold.1 h).1

theorem impll_eg_refl : (EG p) ⋖ p := fun _ _ h => (egc_unfold.1 h).1

/-- `AG p` is idempotent. -/
theorem equivl_ag_idem : (AG p) ⩸ (AG (AG p)) :=
  ⟨le_gfp (b := agcF (agc (entails p))) fun _ _ h => ⟨h, (agc_unfold.1 h).2⟩,
   impll_ag_refl (AG p)⟩

/-- `EG p` is idempotent. -/
theorem equivl_eg_idem : (EG p) ⩸ (EG (EG p)) :=
  ⟨le_gfp (b := egcF (egc (entails p))) fun _ _ h => ⟨h, (egc_unfold.1 h).2⟩,
   impll_eg_refl (EG p)⟩

/-- `AG (p ∧ q)` is `AG p ∧ AG q`. -/
theorem equivl_and_ag : (AG (p ∧ₜ q)) ⩸ ((AG p) ∧ₜ (AG q)) :=
  ⟨fun t w h => ⟨impl_ticl_global .A (p := p ∧ₜ q) (fun _ _ h => h.1) t w h,
                 impl_ticl_global .A (p := p ∧ₜ q) (fun _ _ h => h.2) t w h⟩,
   le_gfp (b := agcF (entails (p ∧ₜ q))) (x := fun t w => agc (entails p) t w ∧ agc (entails q) t w)
     fun _ _ ⟨hp, hq⟩ =>
       let ⟨hp, hs, hkp⟩ := agc_unfold.1 hp
       let ⟨hq, _, hkq⟩ := agc_unfold.1 hq
       ⟨⟨hp, hq⟩, hs, fun t' w' tr => ⟨hkp t' w' tr, hkq t' w' tr⟩⟩⟩

/-- `EG (p ∧ q)` implies `EG p ∧ EG q` (not conversely: the two paths may differ). -/
theorem impll_and_eg : (EG (p ∧ₜ q)) ⋖ ((EG p) ∧ₜ (EG q)) :=
  fun t w h => ⟨impl_ticl_global .E (p := p ∧ₜ q) (fun _ _ h => h.1) t w h,
                impl_ticl_global .E (p := p ∧ₜ q) (fun _ _ h => h.2) t w h⟩

/-- `AG p ∨ AG q` implies `AG (p ∨ q)`. -/
theorem impll_or_ag : ((AG p) ∨ₜ (AG q)) ⋖ (AG (p ∨ₜ q)) :=
  impl_or_impl_and _ _ _
    ⟨impl_ticl_global .A (impl_or_injL p q), impl_ticl_global .A (impl_or_injR p q)⟩

/-- `EG p ∨ EG q` implies `EG (p ∨ q)`. -/
theorem impll_or_eg : ((EG p) ∨ₜ (EG q)) ⋖ (EG (p ∨ₜ q)) :=
  impl_or_impl_and _ _ _
    ⟨impl_ticl_global .E (impl_or_injL p q), impl_ticl_global .E (impl_or_injR p q)⟩

end TicllEquations

-- Not ported: the `Proper` hint externs for `entails`/`entailsL`/`entailsR` (no setoid rewriting;
-- use `impl_ticl_entails`/`equiv_ticl_entails`); the infix notations `⋖L ⩸L ⋖R ⩸R` (the abbrevs
-- `impl_ticll`, `equiv_ticll`, `impl_ticlr`, `equiv_ticlr`).

end Tisl
