/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.Trans
public import Coinductive.Tower

/-!
# Strong simulation

`ss L` is the simulation functor: every `trans` play of the left tree must be answered by a `trans`
play of the right tree, with labels related by `L`. `ssim L` is its greatest fixpoint
(← `Eq/SSim.v`). `CTree` is extensional, so the Rocq up-to-`equ` closures are trivial and omitted.

Rocq `step` on a goal `ssim L t u` is `ssim_unfold.2`; on a hypothesis it is `ssim_unfold.1`.
Coinduction is the `coinduction R hR CIH` tactic; chain elements are unfolded with `step`.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E F C D : Effect.{u}} {X Y X' Y' : Type u}

/-- The strong simulation functor. -/
def ss (L : Label E → Label F → Prop) : Mon (Rel (CTree E C X) (CTree F D Y)) where
  body R t u := ∀ l t', trans l t t' → ∃ l' u', trans l' u u' ∧ R t' u' ∧ L l l'
  mono h _ _ H l t' ht :=
    let ⟨l', u', h₁, h₂, h₃⟩ := H l t' ht
    ⟨l', u', h₁, h _ _ h₂, h₃⟩

/-- Strong simulation. -/
def ssim (L : Label E → Label F → Prop) : Rel (CTree E C X) (CTree F D Y) := gfp (ss L)

/-- Strong simulation with equal labels. -/
scoped infix:50 " ≲ " => ssim Eq

section Heterogeneous
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem ssim_unfold : ssim L t u ↔ ss L (ssim L) t u :=
  ⟨fun h => gfp_pfp (b := ss L) t u h, fun h => b_chain (gfp_chain (ss L)) t u h⟩

/-! Stuck trees are simulated by anything. -/

theorem isStuck_ss (h : isStuck t) : ss L R t u := fun l t' ht => (h l t' ht).elim
theorem isStuck_ssim (h : isStuck t) : ssim L t u := ssim_unfold.2 (isStuck_ss h)
theorem stuck_ss : ss L R (.stuck : CTree E C X) u := isStuck_ss stuck_isStuck
theorem stuck_ssim : ssim L (.stuck : CTree E C X) u := isStuck_ssim stuck_isStuck
theorem spin_ss : ss L R (.spin : CTree E C X) u := isStuck_ss spin_isStuck
theorem spin_ssim : ssim L (.spin : CTree E C X) u := isStuck_ssim spin_isStuck

end Heterogeneous

section Homogeneous
variable {L : Label E → Label E → Prop} {R : Rel (CTree E C X) (CTree E C X)}

theorem ss_chain_refl (hL : ∀ l, L l l) (hR : Chain (ss L) R) : ∀ t, R t t :=
  refl_chain (b := ss L) (fun _ _ ih _ l t' ht => ⟨l, t', ht, ih t', hL l⟩) R hR

theorem ss_chain_trans (hL : ∀ l₁ l₂ l₃, L l₁ l₂ → L l₂ l₃ → L l₁ l₃) (hR : Chain (ss L) R) :
    ∀ t u v, R t u → R u v → R t v :=
  trans_chain (b := ss L) (fun _ _ ih _ _ _ htu huv l t' ht =>
    let ⟨l', u', hu, htu', hl⟩ := htu l t' ht
    let ⟨l'', v', hv, huv', hl'⟩ := huv l' u' hu
    ⟨l'', v', hv, ih _ _ _ htu' huv', hL _ _ _ hl hl'⟩) R hR

theorem ssim_refl (hL : ∀ l, L l l) (t : CTree E C X) : ssim L t t :=
  ss_chain_refl hL (gfp_chain _) t

theorem ssim_trans (hL : ∀ l₁ l₂ l₃, L l₁ l₂ → L l₂ l₃ → L l₁ l₃) {t u v : CTree E C X} :
    ssim L t u → ssim L u v → ssim L t v :=
  ss_chain_trans hL (gfp_chain _) t u v

end Homogeneous

/-! ## Equivalence of label relations on well-formed labels -/

/-- `L` and `L'` agree on labels whose values have types `X` and `Y`. -/
def Lequiv (X Y : Type u) (L L' : Label E → Label F → Prop) : Prop :=
  ∀ l l', WfVal X l → WfVal Y l' → (L l l' ↔ L' l l')

namespace Lequiv
variable {L L' L'' : Label E → Label F → Prop}

theorem refl (L : Label E → Label F → Prop) : Lequiv X Y L L := fun _ _ _ _ => .rfl
theorem symm (h : Lequiv X Y L L') : Lequiv X Y L' L := fun l l' hl hl' => (h l l' hl hl').symm
theorem trans (h₁ : Lequiv X Y L L') (h₂ : Lequiv X Y L' L'') : Lequiv X Y L L'' :=
  fun l l' hl hl' => (h₁ l l' hl hl').trans (h₂ l l' hl hl')

end Lequiv

section LequivSs
variable {L L' : Label E → Label F → Prop}

theorem ss_Lequiv (h : Lequiv X Y L L') (R : Rel (CTree E C X) (CTree F D Y)) :
    ∀ t u, ss L R t u → ss L' R t u := fun _ _ H l t' ht =>
  let ⟨l', u', h₁, h₂, h₃⟩ := H l t' ht
  ⟨l', u', h₁, h₂, (h l l' (wfVal_trans ht) (wfVal_trans h₁)).1 h₃⟩

theorem ssim_Lequiv (h : Lequiv X Y L L') {t : CTree E C X} {u : CTree F D Y} :
    ssim L t u → ssim L' t u :=
  gfp_mono (ss_Lequiv h) t u

end LequivSs

/-! ## Up-to `bind` -/

/-- Relates values by `R0` and non-values by `L`. -/
inductive UpdateValRel (L : Label E → Label F → Prop) (R0 : X → Y → Prop) :
    Label E → Label F → Prop
  | val (v₁ : X) (v₂ : Y) : R0 v₁ v₂ → UpdateValRel L R0 (.val v₁) (.val v₂)
  | nonval (l₁ : Label E) (l₂ : Label F) : ¬ IsVal l₁ → ¬ IsVal l₂ → L l₁ l₂ →
      UpdateValRel L R0 l₁ l₂

namespace UpdateValRel
variable {L : Label E → Label F → Prop} {R0 : X → Y → Prop}

theorem val_l {v₁ : X} {l₂ : Label F} (h : UpdateValRel L R0 (.val v₁) l₂) :
    ∃ v₂ : Y, l₂ = .val v₂ ∧ R0 v₁ v₂ := by
  generalize hl : (Label.val v₁ : Label E) = l₁ at h
  cases h with
  | val _ v₂ h => cases val_eq_inv hl; exact ⟨v₂, rfl, h⟩
  | nonval _ _ h₁ _ _ => exact absurd (hl ▸ .val v₁) h₁

theorem val_r {l₁ : Label E} {v₂ : Y} (h : UpdateValRel L R0 l₁ (.val v₂)) :
    ∃ v₁ : X, l₁ = .val v₁ ∧ R0 v₁ v₂ := by
  generalize hl : (Label.val v₂ : Label F) = l₂ at h
  cases h with
  | val v₁ _ h => cases val_eq_inv hl; exact ⟨v₁, rfl, h⟩
  | nonval _ _ _ h₂ _ => exact absurd (hl ▸ .val v₂) h₂

theorem val_inv {v₁ : X} {v₂ : Y} (h : UpdateValRel L R0 (.val v₁) (.val v₂)) : R0 v₁ v₂ := by
  obtain ⟨_, e, h⟩ := val_l h
  cases val_eq_inv e; exact h

theorem nonval_l {l₁ : Label E} {l₂ : Label F} (h : UpdateValRel L R0 l₁ l₂) (hl : ¬ IsVal l₁) :
    ¬ IsVal l₂ ∧ L l₁ l₂ := by
  cases h with
  | val => exact absurd (.val _) hl
  | nonval _ _ _ h₂ h₃ => exact ⟨h₂, h₃⟩

theorem nonval_r {l₁ : Label E} {l₂ : Label F} (h : UpdateValRel L R0 l₁ l₂) (hl : ¬ IsVal l₂) :
    ¬ IsVal l₁ ∧ L l₁ l₂ := by
  cases h with
  | val => exact absurd (.val _) hl
  | nonval _ _ h₁ _ h₃ => exact ⟨h₁, h₃⟩

instance : RespectsVal (UpdateValRel L R0) where
  respects_val _ _ h := by
    cases h with
    | val => exact ⟨fun _ => .val _, fun _ => .val _⟩
    | nonval _ _ h₁ h₂ _ => exact ⟨fun h => (h₁ h).elim, fun h => (h₂ h).elim⟩

end UpdateValRel

/-- `L0` behaves as `UpdateValRel L R0` on well-formed labels. -/
def isUpdateValRel (L : Label E → Label F → Prop) (R0 : X → Y → Prop)
    (L0 : Label E → Label F → Prop) : Prop :=
  Lequiv X Y (UpdateValRel L R0) L0

theorem updateValRel_correct {L : Label E → Label F → Prop} {R0 : X → Y → Prop} :
    isUpdateValRel L R0 (UpdateValRel L R0) :=
  .refl _

theorem updateValRel_eq : Lequiv X X (UpdateValRel (@Eq (Label E)) (@Eq X)) Eq := by
  intro l l' _ hw'
  constructor
  · rintro (⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> rfl
  · rintro rfl
    cases l with
    | tau => exact .nonval _ _ isVal_tau isVal_tau rfl
    | obs => exact .nonval _ _ isVal_obs isVal_obs rfl
    | val v => cases hw' _ v rfl; exact .val v v rfl

theorem updateValRel_Lequiv {L L' : Label E → Label F → Prop} (h : Lequiv X' Y' L L')
    (R0 : X → Y → Prop) : Lequiv X Y (UpdateValRel L R0) (UpdateValRel L' R0) := by
  intro l l' _ _
  constructor <;> rintro (⟨v₁, v₂, h₀⟩ | ⟨_, _, h₁, h₂, h₃⟩)
  · exact .val _ _ h₀
  · exact .nonval _ _ h₁ h₂ ((h _ _ (wfVal_nonval h₁) (wfVal_nonval h₂)).1 h₃)
  · exact .val _ _ h₀
  · exact .nonval _ _ h₁ h₂ ((h _ _ (wfVal_nonval h₁) (wfVal_nonval h₂)).2 h₃)

theorem isUpdateValRel_Lequiv {L L' : Label E → Label F → Prop} {R0 : X → Y → Prop}
    {L0 L0' : Label E → Label F → Prop} (hL : Lequiv X' Y' L L') (h0 : Lequiv X Y L0 L0')
    (h : isUpdateValRel L' R0 L0') : isUpdateValRel L R0 L0 :=
  (updateValRel_Lequiv hL R0).trans (h.trans h0.symm)

theorem updateValRel_updateValRel {X₀ Y₀ : Type u} (L : Label E → Label F → Prop)
    (R0 : X₀ → Y₀ → Prop) (R1 : X → Y → Prop) (l : Label E) (l' : Label F) :
    UpdateValRel (UpdateValRel L R0) R1 l l' ↔ UpdateValRel L R1 l l' := by
  constructor
  · rintro (⟨v₁, v₂, h⟩ | ⟨_, _, h₁, h₂, h₃⟩)
    · exact .val _ _ h
    · exact .nonval _ _ h₁ h₂ (h₃.nonval_l h₁).2
  · rintro (⟨v₁, v₂, h⟩ | ⟨_, _, h₁, h₂, h₃⟩)
    · exact .val _ _ h
    · exact .nonval _ _ h₁ h₂ (.nonval _ _ h₁ h₂ h₃)

theorem isUpdateValRel_updateValRel_eq {Z : Type u} (R : X → Y → Prop) :
    Lequiv Z Z (UpdateValRel (UpdateValRel (@Eq (Label E)) R) (@Eq Z)) Eq :=
  Lequiv.trans (fun l l' _ _ => updateValRel_updateValRel _ _ _ l l') updateValRel_eq

theorem UpdateValRel.symm {L : Label E → Label E → Prop} {R0 : X → X → Prop}
    (hL : ∀ l l', L l l' → L l' l) (hR : ∀ x y, R0 x y → R0 y x) {l l' : Label E}
    (h : UpdateValRel L R0 l l') : UpdateValRel L R0 l' l := by
  cases h with
  | val _ _ h => exact .val _ _ (hR _ _ h)
  | nonval _ _ h₁ h₂ h₃ => exact .nonval _ _ h₂ h₁ (hL _ _ h₃)

theorem UpdateValRel.trans {L : Label E → Label E → Prop} {R0 : X → X → Prop}
    (hL : ∀ l₁ l₂ l₃, L l₁ l₂ → L l₂ l₃ → L l₁ l₃) (hR : ∀ x y z, R0 x y → R0 y z → R0 x z)
    {l₁ l₂ l₃ : Label E} (h₁ : UpdateValRel L R0 l₁ l₂) (h₂ : UpdateValRel L R0 l₂ l₃) :
    UpdateValRel L R0 l₁ l₃ := by
  cases h₁ with
  | val v₁ v₂ h =>
    obtain ⟨v₃, rfl, h'⟩ := h₂.val_l
    exact .val _ _ (hR _ _ _ h h')
  | nonval _ _ h₁ h₂' h =>
    obtain ⟨h₃, h'⟩ := h₂.nonval_l h₂'
    exact .nonval _ _ h₁ h₃ (hL _ _ _ h h')

/-- `UpdateValRel Eq`. -/
abbrev liftValRel (R0 : X → Y → Prop) : Label E → Label E → Prop := UpdateValRel Eq R0

section Bind
variable {L : Label E → Label F → Prop} {R0 : X → Y → Prop}

/-- Chain elements of `ss L` are closed under `bind`: prefixes related by `ssim RR`, continuations
pointwise by the chain element under `R0`, where `RR` behaves as `UpdateValRel L R0`. -/
theorem ss_chain_bind_gen {RR : Label E → Label F → Prop} (hRR : isUpdateValRel L R0 RR)
    {R : Rel (CTree E C X') (CTree F D Y')} (hR : Chain (ss L) R) :
    ∀ (t : CTree E C X) (t' : CTree F D Y) (k : X → CTree E C X') (k' : Y → CTree F D Y'),
      ssim RR t t' → (∀ x x', R0 x x' → R (k x) (k' x')) → R (t >>= k) (t' >>= k') := by
  refine tower (P := fun R : Rel (CTree E C X') (CTree F D Y') => ∀ t t' k k', ssim RR t t' →
    (∀ x x', R0 x x' → R (k x) (k' x')) → R (t >>= k) (t' >>= k')) ?_ ?_ R hR
  · intro T hT t t' k k' htt' hkk'
    exact Rel.inf_apply.2 fun R hR =>
      hT R hR t t' k k' htt' fun x x' hx => Rel.inf_apply.1 (hkk' x x' hx) R hR
  · intro R hR ih t t' k k' htt' hkk' l u hu
    rcases trans_bind_inv hu with ⟨hl, t₁, ht₁, rfl⟩ | ⟨x, hx, hk⟩
    · obtain ⟨l', t₁', ht₁', hss, hll'⟩ := ssim_unfold.1 htt' l t₁ ht₁
      obtain ⟨hl', hL⟩ :=
        ((hRR l l' (wfVal_trans ht₁) (wfVal_trans ht₁')).2 hll').nonval_l hl
      exact ⟨l', t₁' >>= k', trans_bind_l hl' ht₁',
        ih _ _ _ _ hss fun x x' h => b_chain hR _ _ (hkk' x x' h), hL⟩
    · obtain ⟨l', u', hu', -, hll'⟩ := ssim_unfold.1 htt' _ _ hx
      obtain ⟨v₂, rfl, hv⟩ := ((hRR _ _ (wfVal_trans hx) (wfVal_trans hu')).2 hll').val_l
      cases trans_val_inv hu'
      obtain ⟨l'', u'', hu'', hss', hll''⟩ := hkk' x v₂ hv l u hk
      exact ⟨l'', u'', trans_bind_r hu' hu'', hss', hll''⟩

theorem ssim_clo_bind_gen {L0 : Label E → Label F → Prop} (hL0 : isUpdateValRel L R0 L0)
    {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'} {k₂ : Y → CTree F D Y'}
    (h₁ : ssim L0 t₁ t₂) (h₂ : ∀ x y, R0 x y → ssim L (k₁ x) (k₂ y)) :
    ssim L (t₁ >>= k₁) (t₂ >>= k₂) :=
  ss_chain_bind_gen hL0 (gfp_chain _) _ _ _ _ h₁ h₂

theorem ssim_clo_bind {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'}
    {k₂ : Y → CTree F D Y'} (h₁ : ssim (UpdateValRel L R0) t₁ t₂)
    (h₂ : ∀ x y, R0 x y → ssim L (k₁ x) (k₂ y)) : ssim L (t₁ >>= k₁) (t₂ >>= k₂) :=
  ssim_clo_bind_gen updateValRel_correct h₁ h₂

end Bind

theorem ssim_clo_bind_eq {t₁ : CTree E C X} {t₂ : CTree E D X} {k₁ : X → CTree E C X'}
    {k₂ : X → CTree E D X'} (h₁ : t₁ ≲ t₂) (h₂ : ∀ x, k₁ x ≲ k₂ x) : t₁ >>= k₁ ≲ t₂ >>= k₂ :=
  ssim_clo_bind_gen (R0 := Eq) updateValRel_eq h₁ (by rintro x _ rfl; exact h₂ x)

/-- Rewriting `≲` to the left of a `bind`, inside a chain element. -/
theorem ss_chain_bind {R : Rel (CTree E C Y) (CTree E C Y)} (hR : Chain (ss Eq) R)
    {t t' : CTree E C X} {k k' : X → CTree E C Y} (h₁ : t ≲ t') (h₂ : ∀ x, R (k x) (k' x)) :
    R (t >>= k) (t' >>= k') :=
  ss_chain_bind_gen (R0 := Eq) updateValRel_eq hR _ _ _ _ h₁ (by rintro x _ rfl; exact h₂ x)

/-! ## Proof rules (`Section Proof_Rules`)

Rocq `Proper (equ eq ==> equ eq ==> impl) R` hypotheses are trivial (`equ` is `=`) and dropped. -/

section ProofRules
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}

theorem step_ss_ret_gen (x : X) (y : Y) (hstuck : R .stuck .stuck) (hL : L (.val x) (.val y)) :
    ss L R (pure x : CTree E C X) (pure y : CTree F D Y) := fun l t' ht => by
  obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
  exact ⟨_, _, trans_ret y, hstuck, hL⟩

theorem step_ss_ret (hR : Chain (ss L) R) (x : X) (y : Y) (hL : L (.val x) (.val y)) :
    ss L R (pure x : CTree E C X) (pure y : CTree F D Y) :=
  step_ss_ret_gen x y (b_chain hR _ _ stuck_ss) hL

theorem step_ss_ret_l_gen (x : X) (y : Y) {u u' : CTree F D Y} (hstuck : R .stuck .stuck)
    (hL : L (.val x) (.val y)) (hu : trans (.val y) u u') : ss L R (pure x : CTree E C X) u :=
  fun l t' ht => by
    obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    cases trans_val_inv hu
    exact ⟨_, _, hu, hstuck, hL⟩

theorem step_ss_ret_l (hR : Chain (ss L) R) (x : X) (y : Y) {u u' : CTree F D Y}
    (hL : L (.val x) (.val y)) (hu : trans (.val y) u u') : ss L R (pure x : CTree E C X) u :=
  step_ss_ret_l_gen x y (b_chain hR _ _ stuck_ss) hL hu

theorem ssim_ret (x : X) (y : Y) (hL : L (.val x) (.val y)) :
    ssim L (pure x : CTree E C X) (pure y : CTree F D Y) :=
  ssim_unfold.2 (step_ss_ret (gfp_chain _) x y hL)

/-- `vis` nodes are deterministic in the LTS, so the itree-style rule holds. -/
theorem step_ss_vis_gen (e : E.I) (f : F.I) (k : E.O e → CTree E C X) (k' : F.O f → CTree F D Y)
    (h : ∀ x, ∃ y, R (k x) (k' y) ∧ L (.obs e x) (.obs f y)) : ss L R (.vis e k) (.vis f k') :=
  fun l t' ht => by
    obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
    obtain ⟨y, h₁, h₂⟩ := h x
    exact ⟨_, _, trans_vis y k', h₁, h₂⟩

theorem step_ss_vis (_hR : Chain (ss L) R) (e : E.I) (f : F.I) (k : E.O e → CTree E C X)
    (k' : F.O f → CTree F D Y) (h : ∀ x, ∃ y, R (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    ss L R (.vis e k) (.vis f k') :=
  step_ss_vis_gen e f k k' h

theorem ssim_vis (e : E.I) (f : F.I) (k : E.O e → CTree E C X) (k' : F.O f → CTree F D Y)
    (h : ∀ x, ∃ y, ssim L (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    ssim L (.vis e k) (.vis f k') :=
  ssim_unfold.2 (step_ss_vis_gen e f k k' h)

theorem step_ss_vis_id_gen (e : E.I) (f : F.I) (hO : F.O f = E.O e) (k : E.O e → CTree E C X)
    (k' : F.O f → CTree F D Y) (h : ∀ x, R (k x) (k' (cast hO.symm x)) ∧
      L (.obs e x) (.obs f (cast hO.symm x))) : ss L R (.vis e k) (.vis f k') :=
  step_ss_vis_gen e f k k' fun x => ⟨_, h x⟩

theorem step_ss_vis_id (_hR : Chain (ss L) R) (e : E.I) (f : F.I) (hO : F.O f = E.O e)
    (k : E.O e → CTree E C X) (k' : F.O f → CTree F D Y) (h : ∀ x, R (k x) (k' (cast hO.symm x)) ∧
      L (.obs e x) (.obs f (cast hO.symm x))) : ss L R (.vis e k) (.vis f k') :=
  step_ss_vis_id_gen e f hO k k' h

theorem ssim_vis_id (e : E.I) (f : F.I) (hO : F.O f = E.O e) (k : E.O e → CTree E C X)
    (k' : F.O f → CTree F D Y) (h : ∀ x, ssim L (k x) (k' (cast hO.symm x)) ∧
      L (.obs e x) (.obs f (cast hO.symm x))) : ssim L (.vis e k) (.vis f k') :=
  ssim_unfold.2 (step_ss_vis_id_gen e f hO k k' h)

theorem step_ss_step_gen {t : CTree E C X} {t' : CTree F D Y} (hL : L .tau .tau) (h : R t t') :
    ss L R (.step t) (.step t') := fun l u ht => by
  obtain ⟨rfl, rfl⟩ := trans_step_inv ht
  exact ⟨_, _, trans_step t', h, hL⟩

theorem step_ss_step (_hR : Chain (ss L) R) {t : CTree E C X} {t' : CTree F D Y} (h : R t t')
    (hL : L .tau .tau) : ss L R (.step t) (.step t') :=
  step_ss_step_gen hL h

theorem step_ssim_step {t : CTree E C X} {t' : CTree F D Y} (h : ssim L t t') (hL : L .tau .tau) :
    ssim L (.step t) (.step t') :=
  ssim_unfold.2 (step_ss_step_gen hL h)

/-- Invisible `br` nodes may be killed on the left, but not gone under. -/
theorem step_ss_br_l_gen {c : C.I} {k : C.O c → CTree E C X} {t' : CTree F D Y}
    (h : ∀ x, ss L R (k x) t') : ss L R (.br c k) t' := fun l u ht =>
  let ⟨x, hx⟩ := trans_br_inv ht; h x l u hx

theorem step_ss_br_l (_hR : Chain (ss L) R) {c : C.I} {k : C.O c → CTree E C X}
    {t : CTree F D Y} (h : ∀ x, ss L R (k x) t) : ss L R (.br c k) t :=
  step_ss_br_l_gen h

theorem ssim_br_l {c : C.I} {k : C.O c → CTree E C X} {t : CTree F D Y}
    (h : ∀ x, ssim L (k x) t) : ssim L (.br c k) t :=
  ssim_unfold.2 (step_ss_br_l_gen fun x => ssim_unfold.1 (h x))

theorem step_ss_br_r_gen {c : D.I} (x : D.O c) {k : D.O c → CTree F D Y} {t : CTree E C X}
    (h : ss L R t (k x)) : ss L R t (.br c k) := fun l t' ht =>
  let ⟨l', u', hu, h₁, h₂⟩ := h l t' ht; ⟨l', u', trans_br x hu, h₁, h₂⟩

theorem step_ss_br_r (_hR : Chain (ss L) R) {c : D.I} (x : D.O c) {k : D.O c → CTree F D Y}
    {t : CTree E C X} (h : ss L R t (k x)) : ss L R t (.br c k) :=
  step_ss_br_r_gen x h

theorem ssim_br_r {c : D.I} (x : D.O c) {k : D.O c → CTree F D Y} {t : CTree E C X}
    (h : ssim L t (k x)) : ssim L t (.br c k) :=
  ssim_unfold.2 (step_ss_br_r_gen x (ssim_unfold.1 h))

theorem step_ss_br_gen {a : C.I} {b : D.I} {k : C.O a → CTree E C X} {k' : D.O b → CTree F D Y}
    (h : ∀ x, ∃ y, ss L R (k x) (k' y)) : ss L R (.br a k) (.br b k') :=
  step_ss_br_l_gen fun x => let ⟨y, hy⟩ := h x; step_ss_br_r_gen y hy

theorem step_ss_br (_hR : Chain (ss L) R) {a : C.I} {b : D.I} {k : C.O a → CTree E C X}
    {k' : D.O b → CTree F D Y} (h : ∀ x, ∃ y, ss L R (k x) (k' y)) :
    ss L R (.br a k) (.br b k') :=
  step_ss_br_gen h

theorem ssim_br {a : C.I} {b : D.I} {k : C.O a → CTree E C X} {k' : D.O b → CTree F D Y}
    (h : ∀ x, ∃ y, ssim L (k x) (k' y)) : ssim L (.br a k) (.br b k') :=
  ssim_unfold.2 (step_ss_br_gen fun x => let ⟨y, hy⟩ := h x; ⟨y, ssim_unfold.1 hy⟩)

theorem step_ss_br_id_gen {a : C.I} {b : D.I} (hO : D.O b = C.O a) {k : C.O a → CTree E C X}
    {k' : D.O b → CTree F D Y} (h : ∀ x, ss L R (k x) (k' (cast hO.symm x))) :
    ss L R (.br a k) (.br b k') :=
  step_ss_br_gen fun x => ⟨_, h x⟩

theorem step_ss_br_id (_hR : Chain (ss L) R) {a : C.I} {b : D.I} (hO : D.O b = C.O a)
    {k : C.O a → CTree E C X} {k' : D.O b → CTree F D Y}
    (h : ∀ x, ss L R (k x) (k' (cast hO.symm x))) : ss L R (.br a k) (.br b k') :=
  step_ss_br_id_gen hO h

theorem ssim_br_id {a : C.I} {b : D.I} (hO : D.O b = C.O a) {k : C.O a → CTree E C X}
    {k' : D.O b → CTree F D Y} (h : ∀ x, ssim L (k x) (k' (cast hO.symm x))) :
    ssim L (.br a k) (.br b k') :=
  ssim_br fun x => ⟨_, h x⟩

theorem step_ss_guard_gen {t : CTree E C X} {t' : CTree F D Y} (h : ss L R t t') :
    ss L R (.guard t) (.guard t') := fun l u ht =>
  let ⟨l', u', hu, h₁, h₂⟩ := h l u (trans_guard_inv ht); ⟨l', u', trans_guard hu, h₁, h₂⟩

theorem step_ss_guard_l_gen {t : CTree E C X} {t' : CTree F D Y} (h : ss L R t t') :
    ss L R (.guard t) t' := fun l u ht => h l u (trans_guard_inv ht)

theorem step_ss_guard_r_gen {t : CTree E C X} {t' : CTree F D Y} (h : ss L R t t') :
    ss L R t (.guard t') := fun l u ht =>
  let ⟨l', u', hu, h₁, h₂⟩ := h l u ht; ⟨l', u', trans_guard hu, h₁, h₂⟩

theorem step_ss_guard_l (_hR : Chain (ss L) R) {t : CTree E C X} {t' : CTree F D Y}
    (h : ss L R t t') : ss L R (.guard t) t' := step_ss_guard_l_gen h
theorem step_ss_guard_r (_hR : Chain (ss L) R) {t : CTree E C X} {t' : CTree F D Y}
    (h : ss L R t t') : ss L R t (.guard t') := step_ss_guard_r_gen h
theorem step_ss_guard (_hR : Chain (ss L) R) {t : CTree E C X} {t' : CTree F D Y}
    (h : ss L R t t') : ss L R (.guard t) (.guard t') := step_ss_guard_gen h

theorem ssim_guard_l {t : CTree E C X} {t' : CTree F D Y} (h : ssim L t t') :
    ssim L (.guard t) t' := ssim_unfold.2 (step_ss_guard_l_gen (ssim_unfold.1 h))
theorem ssim_guard_r {t : CTree E C X} {t' : CTree F D Y} (h : ssim L t t') :
    ssim L t (.guard t') := ssim_unfold.2 (step_ss_guard_r_gen (ssim_unfold.1 h))
theorem ssim_guard {t : CTree E C X} {t' : CTree F D Y} (h : ssim L t t') :
    ssim L (.guard t) (.guard t') := ssim_unfold.2 (step_ss_guard_gen (ssim_unfold.1 h))

theorem step_ss_brS_gen {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (h : ∀ x, ∃ y, R (k x) (k' y)) (hL : L .tau .tau) : ss L R (.brS c k) (.brS d k') :=
  step_ss_br_gen fun x => let ⟨y, hy⟩ := h x; ⟨y, step_ss_step_gen hL hy⟩

theorem step_ss_brS (_hR : Chain (ss L) R) {c : C.I} {d : D.I} {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, ∃ y, R (k x) (k' y)) (hL : L .tau .tau) :
    ss L R (.brS c k) (.brS d k') :=
  step_ss_brS_gen h hL

theorem ssim_brS {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (h : ∀ x, ∃ y, ssim L (k x) (k' y)) (hL : L .tau .tau) : ssim L (.brS c k) (.brS d k') :=
  ssim_br fun x => let ⟨y, hy⟩ := h x; ⟨y, step_ssim_step hy hL⟩

theorem step_ss_brS_id_gen {c : C.I} {d : D.I} (hO : D.O d = C.O c) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, R (k x) (k' (cast hO.symm x))) (hL : L .tau .tau) :
    ss L R (.brS c k) (.brS d k') :=
  step_ss_brS_gen (fun x => ⟨_, h x⟩) hL

theorem step_ss_brS_id (_hR : Chain (ss L) R) {c : C.I} {d : D.I} (hO : D.O d = C.O c)
    {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y} (h : ∀ x, R (k x) (k' (cast hO.symm x)))
    (hL : L .tau .tau) : ss L R (.brS c k) (.brS d k') :=
  step_ss_brS_id_gen hO h hL

theorem ssim_brS_id {c : C.I} {d : D.I} (hO : D.O d = C.O c) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, ssim L (k x) (k' (cast hO.symm x))) (hL : L .tau .tau) :
    ssim L (.brS c k) (.brS d k') :=
  ssim_brS (fun x => ⟨_, h x⟩) hL

/-- Visible `n`-ary spins simulate each other when the target spin has a branch. -/
theorem ssim_spinS_gen_nonempty {c : C.I} {d : D.I} (y : D.O d) (hL : L .tau .tau) :
    ssim L (CTree.spinS_gen c : CTree E C X) (CTree.spinS_gen d : CTree F D Y) := by
  coinduction _ _ CIH
  rw [unfold_spinS_gen c, unfold_spinS_gen d]
  exact step_ss_brS_gen (fun _ => ⟨y, CIH⟩) hL

/-! ### Inversion principles -/

theorem ssim_ret_inv {r₁ : X} {r₂ : Y} (h : ssim L (pure r₁ : CTree E C X) (pure r₂ : CTree F D Y)) :
    L (.val r₁) (.val r₂) := by
  obtain ⟨l', u', hu, -, hl⟩ := ssim_unfold.1 h _ _ (trans_ret r₁)
  obtain ⟨-, rfl⟩ := trans_ret_inv hu
  exact hl

theorem ss_ret_l_inv {r : X} {u : CTree F D Y} (h : ss L R (pure r : CTree E C X) u) :
    ∃ l' u', trans l' u u' ∧ R .stuck u' ∧ L (.val r) l' :=
  h _ _ (trans_ret r)

theorem ssim_ret_l_inv {r : X} {u : CTree F D Y} (h : ssim L (pure r : CTree E C X) u) :
    ∃ l' u', trans l' u u' ∧ L (.val r) l' :=
  let ⟨l', u', hu, _, hl⟩ := ss_ret_l_inv (ssim_unfold.1 h); ⟨l', u', hu, hl⟩

/-- Rocq concludes equality of answer types; with `Effect` this is equality of the events. -/
theorem ssim_vis_inv_type {e₁ e₂ : E.I} {k₁ : E.O e₁ → CTree E C X} {k₂ : E.O e₂ → CTree E D Y}
    (x₁ : E.O e₁) (h : ssim Eq (.vis e₁ k₁) (.vis e₂ k₂)) : e₁ = e₂ := by
  obtain ⟨l', u', hu, -, rfl⟩ := ssim_unfold.1 h _ _ (trans_vis x₁ k₁)
  obtain ⟨_, -, hl⟩ := trans_vis_inv hu
  exact (obs_eq_inv hl).1

theorem ssbt_vis_inv (_hR : Chain (ss L) R) {e₁ : E.I} {e₂ : F.I} {k₁ : E.O e₁ → CTree E C X}
    {k₂ : F.O e₂ → CTree F D Y} (x : E.O e₁) (h : ss L R (.vis e₁ k₁) (.vis e₂ k₂)) :
    (∃ y, L (.obs e₁ x) (.obs e₂ y)) ∧ ∀ x, ∃ y, R (k₁ x) (k₂ y) := by
  refine ⟨?_, fun x => ?_⟩ <;>
  · obtain ⟨l', u', hu, hR', hl⟩ := h _ _ (trans_vis x k₁)
    obtain ⟨y, rfl, rfl⟩ := trans_vis_inv hu
    first | exact ⟨y, hl⟩ | exact ⟨y, hR'⟩

theorem ssim_vis_inv {e₁ : E.I} {e₂ : F.I} {k₁ : E.O e₁ → CTree E C X}
    {k₂ : F.O e₂ → CTree F D Y} (x : E.O e₁) (h : ssim L (.vis e₁ k₁) (.vis e₂ k₂)) :
    (∃ y, L (.obs e₁ x) (.obs e₂ y)) ∧ ∀ x, ∃ y, ssim L (k₁ x) (k₂ y) :=
  ssbt_vis_inv (gfp_chain _) x (ssim_unfold.1 h)

theorem ss_vis_l_inv {e : E.I} {k : E.O e → CTree E C X} {u : CTree F D Y} (x : E.O e)
    (h : ss L R (.vis e k) u) : ∃ l' u', trans l' u u' ∧ R (k x) u' ∧ L (.obs e x) l' :=
  h _ _ (trans_vis x k)

theorem ssim_vis_l_inv {e : E.I} {k : E.O e → CTree E C X} {u : CTree F D Y} (x : E.O e)
    (h : ssim L (.vis e k) u) : ∃ l' u', trans l' u u' ∧ ssim L (k x) u' ∧ L (.obs e x) l' :=
  ss_vis_l_inv x (ssim_unfold.1 h)

theorem ss_step_inv (_hR : Chain (ss L) R) {t₁ : CTree E C X} {t₂ : CTree F D Y}
    (h : ss L R (.step t₁) (.step t₂)) : R t₁ t₂ := by
  obtain ⟨_, _, hu, h', -⟩ := h _ _ (trans_step t₁)
  obtain ⟨rfl, -⟩ := trans_step_inv hu
  exact h'

theorem ssim_step_inv {t₁ : CTree E C X} {t₂ : CTree F D Y}
    (h : ssim L (.step t₁) (.step t₂)) : ssim L t₁ t₂ :=
  ss_step_inv (gfp_chain _) (ssim_unfold.1 h)

theorem ss_step_l_inv {t : CTree E C X} {u : CTree F D Y} (h : ss L R (.step t) u) :
    ∃ l' u', trans l' u u' ∧ R t u' ∧ L .tau l' :=
  h _ _ (trans_step t)

theorem ssim_step_l_inv {t : CTree E C X} {u : CTree F D Y} (h : ssim L (.step t) u) :
    ∃ l' u', trans l' u u' ∧ ssim L t u' ∧ L .tau l' :=
  ss_step_l_inv (ssim_unfold.1 h)

theorem ssbt_brS_inv (_hR : Chain (ss L) R) {c : C.I} {d : D.I} {k₁ : C.O c → CTree E C X}
    {k₂ : D.O d → CTree F D Y} (h : ss L R (.brS c k₁) (.brS d k₂)) :
    ∀ i₁, ∃ i₂, R (k₁ i₁) (k₂ i₂) := fun i₁ => by
  obtain ⟨_, _, hu, h', -⟩ := h _ _ (trans_brS k₁ i₁)
  obtain ⟨i₂, rfl, -⟩ := trans_brS_inv hu
  exact ⟨i₂, h'⟩

theorem ssim_brS_inv {c : C.I} {d : D.I} {k₁ : C.O c → CTree E C X} {k₂ : D.O d → CTree F D Y}
    (h : ssim L (.brS c k₁) (.brS d k₂)) : ∀ i₁, ∃ i₂, ssim L (k₁ i₁) (k₂ i₂) :=
  ssbt_brS_inv (gfp_chain _) (ssim_unfold.1 h)

theorem ss_brS_l_inv {c : C.I} {k : C.O c → CTree E C X} {u : CTree F D Y} (x : C.O c)
    (h : ss L R (.brS c k) u) : ∃ l' u', trans l' u u' ∧ R (k x) u' ∧ L .tau l' :=
  h _ _ (trans_brS k x)

theorem ssim_brS_l_inv {c : C.I} {k : C.O c → CTree E C X} {u : CTree F D Y} (x : C.O c)
    (h : ssim L (.brS c k) u) : ∃ l' u', trans l' u u' ∧ ssim L (k x) u' ∧ L .tau l' :=
  ss_brS_l_inv x (ssim_unfold.1 h)

theorem ss_br_l_inv {c : C.I} {t : CTree F D Y} {k : C.O c → CTree E C X}
    (h : ss L R (.br c k) t) (x : C.O c) : ss L R (k x) t := fun l u hu =>
  h l u (trans_br x hu)

theorem ssim_br_l_inv {c : C.I} {t : CTree F D Y} {k : C.O c → CTree E C X}
    (h : ssim L (.br c k) t) (x : C.O c) : ssim L (k x) t :=
  ssim_unfold.2 (ss_br_l_inv (ssim_unfold.1 h) x)

theorem ss_guard_l_inv {t : CTree E C X} {u : CTree F D Y} (h : ss L R (.guard t) u) :
    ss L R t u := fun l u' hu => h l u' (trans_guard hu)

theorem ssim_guard_l_inv {t : CTree E C X} {u : CTree F D Y} (h : ssim L (.guard t) u) :
    ssim L t u := ssim_unfold.2 (ss_guard_l_inv (ssim_unfold.1 h))

theorem ssim_br_r_inv {c : D.I} {t : CTree E C X} {k : D.O c → CTree F D Y}
    (h : ssim L t (.br c k)) {l : Label E} {t' : CTree E C X} (ht : trans l t t') :
    ∃ l' x t'', trans l' (k x) t'' ∧ L l l' ∧ ssim L t' t'' := by
  obtain ⟨l', u', hu, h', hl⟩ := ssim_unfold.1 h l t' ht
  obtain ⟨x, hx⟩ := trans_br_inv hu
  exact ⟨l', x, u', hx, hl, h'⟩

end ProofRules

end CTree
