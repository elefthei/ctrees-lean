/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.SSim

/-!
# Complete strong simulation

`css L` strengthens `ss L` with a progress condition: whenever the right tree can step, so can the
left one. `cssim L` is its greatest fixpoint (← `Eq/CSSim.v`). Up-to-`equ` closures and `Proper`
instances are omitted (equality is extensional); the `Proper` hypotheses of the `*_gen` rules are
vacuous, so the Rocq chain variants are subsumed by them unless they need the chain.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E F C D : Effect.{u}} {X Y X' Y' : Type u}

/-- The complete strong simulation functor. -/
def css (L : Label E → Label F → Prop) : Mon (Rel (CTree E C X) (CTree F D Y)) where
  body R t u := ss L R t u ∧ ∀ l u', trans l u u' → ∃ l' t', trans l' t t'
  mono h t u H := ⟨(ss L).mono h t u H.1, H.2⟩

/-- Complete strong simulation. -/
def cssim (L : Label E → Label F → Prop) : Rel (CTree E C X) (CTree F D Y) := gfp (css L)

/-- Complete strong simulation with equal labels. -/
scoped infix:50 " ⪅ " => cssim Eq

section Heterogeneous
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem cssim_unfold : cssim L t u ↔ css L (cssim L) t u :=
  ⟨fun h => gfp_pfp (b := css L) t u h, fun h => b_chain (gfp_chain (css L)) t u h⟩

theorem cssim_subrelation {L' : Label E → Label F → Prop} (hL : ∀ l l', L l l' → L' l l') :
    cssim L t u → cssim L' t u :=
  gfp_mono (b := css L) (c := css L') (fun _ _ _ H =>
    ⟨fun l t' ht => let ⟨l', u', h₁, h₂, h₃⟩ := H.1 l t' ht; ⟨l', u', h₁, h₂, hL _ _ h₃⟩, H.2⟩) t u

theorem isStuck_css (h : css L R t u) : isStuck t ↔ isStuck u :=
  ⟨fun hs l u' hu => let ⟨_, _, ht⟩ := h.2 l u' hu; hs _ _ ht,
   fun hs l t' ht => let ⟨_, _, hu, _⟩ := h.1 l t' ht; hs _ _ hu⟩

theorem isStuck_cssim (h : cssim L t u) : isStuck t ↔ isStuck u := isStuck_css (cssim_unfold.1 h)

theorem css_isStuck (ht : isStuck t) (hu : isStuck u) : css L R t u :=
  ⟨isStuck_ss ht, fun _ _ h => (hu _ _ h).elim⟩

theorem cssim_isStuck (ht : isStuck t) (hu : isStuck u) : cssim L t u :=
  cssim_unfold.2 (css_isStuck ht hu)

theorem cssim_ssim_subrelation_gen : cssim L t u → ssim L t u :=
  gfp_mono (b := css L) (c := ss L) (fun _ _ _ H => H.1) t u

end Heterogeneous

section Homogeneous
variable {L : Label E → Label E → Prop} {R : Rel (CTree E C X) (CTree E C X)}

theorem css_chain_refl (hL : ∀ l, L l l) (hR : Chain (css L) R) : ∀ t, R t t :=
  refl_chain (b := css L)
    (fun _ _ ih _ => ⟨fun l t' ht => ⟨l, t', ht, ih t', hL l⟩, fun l u' h => ⟨l, u', h⟩⟩) R hR

theorem css_chain_trans (hL : ∀ l₁ l₂ l₃, L l₁ l₂ → L l₂ l₃ → L l₁ l₃) (hR : Chain (css L) R) :
    ∀ t u v, R t u → R u v → R t v :=
  trans_chain (b := css L) (fun _ _ ih _ _ _ htu huv =>
    ⟨fun l t' ht =>
      let ⟨l', u', hu, htu', hl⟩ := htu.1 l t' ht
      let ⟨l'', v', hv, huv', hl'⟩ := huv.1 l' u' hu
      ⟨l'', v', hv, ih _ _ _ htu' huv', hL _ _ _ hl hl'⟩,
     fun l v' hv =>
      let ⟨_, _, hu⟩ := huv.2 l v' hv
      htu.2 _ _ hu⟩) R hR

theorem cssim_refl (hL : ∀ l, L l l) (t : CTree E C X) : cssim L t t :=
  css_chain_refl hL (gfp_chain _) t

theorem cssim_trans (hL : ∀ l₁ l₂ l₃, L l₁ l₂ → L l₂ l₃ → L l₁ l₃) {t u v : CTree E C X} :
    cssim L t u → cssim L u v → cssim L t v :=
  css_chain_trans hL (gfp_chain _) t u v

theorem cssim_ssim_subrelation {t u : CTree E C X} : cssim L t u → ssim L t u :=
  cssim_ssim_subrelation_gen

end Homogeneous

/-! ## Up-to `bind` -/

section Bind
variable {L : Label E → Label F → Prop} {R0 : X → Y → Prop}

/-- Chain elements of `css L` are closed under `bind`: prefixes related by `cssim RR`, continuations
pointwise by the chain element under `R0` and making progress on the left. -/
theorem css_chain_bind_gen {RR : Label E → Label F → Prop} (hRR : isUpdateValRel L R0 RR)
    {R : Rel (CTree E C X') (CTree F D Y')} (hR : Chain (css L) R) :
    ∀ (t : CTree E C X) (t' : CTree F D Y) (k : X → CTree E C X') (k' : Y → CTree F D Y'),
      cssim RR t t' → (∀ x x', R0 x x' → R (k x) (k' x') ∧ ∃ l t'', trans l (k x) t'') →
      R (t >>= k) (t' >>= k') := by
  refine tower (P := fun R : Rel (CTree E C X') (CTree F D Y') => ∀ t t' k k', cssim RR t t' →
    (∀ x x', R0 x x' → R (k x) (k' x') ∧ ∃ l t'', trans l (k x) t'') →
      R (t >>= k) (t' >>= k')) ?_ ?_ R hR
  · intro T hT t t' k k' htt' hkk'
    exact Rel.inf_apply.2 fun R hR =>
      hT R hR t t' k k' htt' fun x x' hx =>
        ⟨Rel.inf_apply.1 (hkk' x x' hx).1 R hR, (hkk' x x' hx).2⟩
  · intro R hR ih t t' k k' htt' hkk'
    obtain ⟨hf, hb⟩ := cssim_unfold.1 htt'
    refine ⟨fun l u hu => ?_, fun l u hu => ?_⟩
    · rcases trans_bind_inv hu with ⟨hl, t₁, ht₁, rfl⟩ | ⟨x, hx, hk⟩
      · obtain ⟨l', t₁', ht₁', hss, hll'⟩ := hf l t₁ ht₁
        obtain ⟨hl', hL⟩ :=
          ((hRR l l' (wfVal_trans ht₁) (wfVal_trans ht₁')).2 hll').nonval_l hl
        exact ⟨l', t₁' >>= k', trans_bind_l hl' ht₁',
          ih _ _ _ _ hss fun x x' h => ⟨b_chain hR _ _ (hkk' x x' h).1, (hkk' x x' h).2⟩, hL⟩
      · obtain ⟨l', u', hu', -, hll'⟩ := hf _ _ hx
        obtain ⟨v₂, rfl, hv⟩ := ((hRR _ _ (wfVal_trans hx) (wfVal_trans hu')).2 hll').val_l
        cases trans_val_inv hu'
        obtain ⟨l'', u'', hu'', hss', hll''⟩ := (hkk' x v₂ hv).1.1 l u hk
        exact ⟨l'', u'', trans_bind_r hu' hu'', hss', hll''⟩
    · obtain ⟨l', t₂', ht₂'⟩ := trans_bind_inv_l hu
      obtain ⟨l'', t₁', ht₁'⟩ := hb l' t₂' ht₂'
      by_cases hv : IsVal l''
      · obtain ⟨x, rfl⟩ := wfVal_isVal_inv hv (wfVal_trans ht₁')
        cases trans_val_inv ht₁'
        obtain ⟨l₃, u₃, hu₃, -, hl₃⟩ := hf _ _ ht₁'
        obtain ⟨v₂, rfl, hx⟩ := ((hRR _ _ (wfVal_trans ht₁') (wfVal_trans hu₃)).2 hl₃).val_l
        obtain ⟨l₄, t₄, h₄⟩ := (hkk' x v₂ hx).2
        exact ⟨l₄, t₄, trans_bind_r ht₁' h₄⟩
      · exact ⟨l'', _, trans_bind_l hv ht₁'⟩

theorem cssim_clo_bind_gen {L0 : Label E → Label F → Prop} (hL0 : isUpdateValRel L R0 L0)
    {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'} {k₂ : Y → CTree F D Y'}
    (h₁ : cssim L0 t₁ t₂) (h₂ : ∀ x y, R0 x y → cssim L (k₁ x) (k₂ y))
    (hp : ∀ x, ∃ l t', trans l (k₁ x) t') : cssim L (t₁ >>= k₁) (t₂ >>= k₂) :=
  css_chain_bind_gen hL0 (gfp_chain _) _ _ _ _ h₁ fun x y h => ⟨h₂ x y h, hp x⟩

theorem cssim_clo_bind {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'}
    {k₂ : Y → CTree F D Y'} (h₁ : cssim (UpdateValRel L R0) t₁ t₂)
    (h₂ : ∀ x y, R0 x y → cssim L (k₁ x) (k₂ y)) (hp : ∀ x, ∃ l t', trans l (k₁ x) t') :
    cssim L (t₁ >>= k₁) (t₂ >>= k₂) :=
  cssim_clo_bind_gen updateValRel_correct h₁ h₂ hp

end Bind

theorem cssim_clo_bind_eq {t₁ : CTree E C X} {t₂ : CTree E D X} {k₁ : X → CTree E C X'}
    {k₂ : X → CTree E D X'} (h₁ : t₁ ⪅ t₂) (h₂ : ∀ x, k₁ x ⪅ k₂ x)
    (hp : ∀ x, ∃ l t', trans l (k₁ x) t') : t₁ >>= k₁ ⪅ t₂ >>= k₂ :=
  cssim_clo_bind_gen (R0 := Eq) updateValRel_eq h₁ (by rintro x _ rfl; exact h₂ x) hp

/-! ## Proof rules -/

section ProofRules
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}

theorem step_css_ret_gen {x : X} {y : Y} (hst : R .stuck .stuck) (hL : L (.val x) (.val y)) :
    css L R (pure x) (pure y) :=
  ⟨fun l t' ht => by
    obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    exact ⟨_, _, trans_ret y, hst, hL⟩,
   fun _ _ _ => ⟨_, _, trans_ret x⟩⟩

theorem step_css_ret {x : X} {y : Y} (hR : Chain (css L) R) (hL : L (.val x) (.val y)) :
    css L R (pure x) (pure y) :=
  step_css_ret_gen (b_chain hR _ _ (css_isStuck stuck_isStuck stuck_isStuck)) hL

theorem step_css_ret_l_gen {x : X} {y : Y} {u u' : CTree F D Y} (hst : R .stuck .stuck)
    (hL : L (.val x) (.val y)) (hu : trans (.val y) u u') : css L R (pure x) u :=
  ⟨fun l t' ht => by
    obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    cases trans_val_inv hu
    exact ⟨_, _, hu, hst, hL⟩,
   fun _ _ _ => ⟨_, _, trans_ret x⟩⟩

theorem step_css_ret_l {x : X} {y : Y} {u u' : CTree F D Y} (hR : Chain (css L) R)
    (hL : L (.val x) (.val y)) (hu : trans (.val y) u u') : css L R (pure x) u :=
  step_css_ret_l_gen (b_chain hR _ _ (css_isStuck stuck_isStuck stuck_isStuck)) hL hu

theorem cssim_ret {x : X} {y : Y} (hL : L (.val x) (.val y)) :
    cssim L (pure x : CTree E C X) (pure y : CTree F D Y) :=
  cssim_unfold.2 (step_css_ret (gfp_chain _) hL)

theorem step_css_vis_gen {e : E.I} {f : F.I} {k : E.O e → CTree E C X} {k' : F.O f → CTree F D Y}
    (hne : Nonempty (E.O e)) (h : ∀ x, ∃ y, R (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    css L R (.vis e k) (.vis f k') :=
  ⟨fun l t' ht => by
    obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
    obtain ⟨y, h₁, h₂⟩ := h x
    exact ⟨_, _, trans_vis y k', h₁, h₂⟩,
   fun _ _ _ => ⟨_, _, trans_vis (Classical.choice hne) k⟩⟩

theorem cssim_vis {e : E.I} {f : F.I} {k : E.O e → CTree E C X} {k' : F.O f → CTree F D Y}
    (hne : Nonempty (E.O e)) (h : ∀ x, ∃ y, cssim L (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    cssim L (.vis e k) (.vis f k') :=
  cssim_unfold.2 (step_css_vis_gen hne h)

/-- Rocq's `Z` shared by `e : E Z` and `f : F Z` becomes the type equation `hO`. -/
theorem step_css_vis_id_gen {e : E.I} {f : F.I} (hO : E.O e = F.O f) {k : E.O e → CTree E C X}
    {k' : F.O f → CTree F D Y}
    (h : ∀ x, R (k x) (k' (cast hO x)) ∧ L (.obs e x) (.obs f (cast hO x))) :
    css L R (.vis e k) (.vis f k') :=
  ⟨fun l t' ht => by
    obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
    exact ⟨_, _, trans_vis _ k', (h x).1, (h x).2⟩,
   fun _ _ hu => by
    obtain ⟨y, -, -⟩ := trans_vis_inv hu
    exact ⟨_, _, trans_vis (cast hO.symm y) k⟩⟩

theorem cssim_vis_id {e : E.I} {f : F.I} (hO : E.O e = F.O f) {k : E.O e → CTree E C X}
    {k' : F.O f → CTree F D Y}
    (h : ∀ x, cssim L (k x) (k' (cast hO x)) ∧ L (.obs e x) (.obs f (cast hO x))) :
    cssim L (.vis e k) (.vis f k') :=
  cssim_unfold.2 (step_css_vis_id_gen hO h)

theorem step_css_step_gen {t : CTree E C X} {t' : CTree F D Y} (hL : L .tau .tau) (h : R t t') :
    css L R (.step t) (.step t') :=
  ⟨fun l t'' ht => by
    obtain ⟨rfl, rfl⟩ := trans_step_inv ht
    exact ⟨_, _, trans_step t', h, hL⟩,
   fun _ _ _ => ⟨_, _, trans_step t⟩⟩

theorem cssim_step {t : CTree E C X} {t' : CTree F D Y} (h : cssim L t t') (hL : L .tau .tau) :
    cssim L (.step t) (.step t') :=
  cssim_unfold.2 (step_css_step_gen hL h)

theorem step_css_br_l_gen {c : C.I} {k : C.O c → CTree E C X} {t' : CTree F D Y}
    (hne : Nonempty (C.O c)) (h : ∀ x, css L R (k x) t') : css L R (.br c k) t' :=
  ⟨fun l t'' ht => let ⟨n, ht⟩ := trans_br_inv ht; (h n).1 l t'' ht,
   fun l u hu => let ⟨_, _, ht⟩ := (h (Classical.choice hne)).2 l u hu; ⟨_, _, trans_br _ ht⟩⟩

theorem cssim_br_l {c : C.I} {k : C.O c → CTree E C X} {t' : CTree F D Y}
    (hne : Nonempty (C.O c)) (h : ∀ x, cssim L (k x) t') : cssim L (.br c k) t' :=
  cssim_unfold.2 (step_css_br_l_gen hne fun x => cssim_unfold.1 (h x))

/-- Needs explicit progress of `t`: if `k z` is stuck, `t` is too, but `.br d k` may still step. -/
theorem step_css_br_r_gen {d : D.I} {t : CTree E C X} {k : D.O d → CTree F D Y} (z : D.O d)
    (hp : ∃ l t', trans l t t') (h : css L R t (k z)) : css L R t (.br d k) :=
  ⟨fun l t' ht => let ⟨l', u', hu, h₁, h₂⟩ := h.1 l t' ht; ⟨l', u', trans_br z hu, h₁, h₂⟩,
   fun _ _ _ => hp⟩

theorem cssim_br_r {d : D.I} {t : CTree E C X} {k : D.O d → CTree F D Y} (z : D.O d)
    (hp : ∃ l t', trans l t t') (h : cssim L t (k z)) : cssim L t (.br d k) :=
  cssim_unfold.2 (step_css_br_r_gen z hp (cssim_unfold.1 h))

theorem step_css_br_gen {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (hp : ∃ x l t', trans l (k x) t') (h : ∀ x, ∃ y, css L R (k x) (k' y)) :
    css L R (.br c k) (.br d k') :=
  ⟨fun l t' ht =>
    let ⟨n, ht⟩ := trans_br_inv ht
    let ⟨y, hy⟩ := h n
    let ⟨l', u', hu, h₁, h₂⟩ := hy.1 l t' ht
    ⟨l', u', trans_br y hu, h₁, h₂⟩,
   fun _ _ _ => let ⟨x, _, _, ht⟩ := hp; ⟨_, _, trans_br x ht⟩⟩

theorem cssim_br {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (hp : ∃ x l t', trans l (k x) t') (h : ∀ x, ∃ y, cssim L (k x) (k' y)) :
    cssim L (.br c k) (.br d k') :=
  cssim_unfold.2 (step_css_br_gen hp fun x =>
    let ⟨y, hy⟩ := h x; ⟨y, cssim_unfold.1 hy⟩)

theorem step_css_br_id_gen {c : C.I} {d : D.I} (hO : C.O c = D.O d) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, css L R (k x) (k' (cast hO x))) :
    css L R (.br c k) (.br d k') :=
  ⟨fun l t' ht =>
    let ⟨n, ht⟩ := trans_br_inv ht
    let ⟨l', u', hu, h₁, h₂⟩ := (h n).1 l t' ht
    ⟨l', u', trans_br _ hu, h₁, h₂⟩,
   fun l u hu => by
    obtain ⟨n, hu⟩ := trans_br_inv hu
    obtain ⟨_, _, ht⟩ := (h (cast hO.symm n)).2 l u (by simpa using hu)
    exact ⟨_, _, trans_br _ ht⟩⟩

theorem cssim_br_id {c : C.I} {d : D.I} (hO : C.O c = D.O d) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, cssim L (k x) (k' (cast hO x))) :
    cssim L (.br c k) (.br d k') :=
  cssim_unfold.2 (step_css_br_id_gen hO fun x => cssim_unfold.1 (h x))

theorem step_css_guard_gen {t : CTree E C X} {t' : CTree F D Y} (h : css L R t t') :
    css L R (.guard t) (.guard t') :=
  ⟨fun l t'' ht =>
    let ⟨l', u', hu, h₁, h₂⟩ := h.1 l t'' (trans_guard_inv ht)
    ⟨l', u', trans_guard hu, h₁, h₂⟩,
   fun l u hu => let ⟨_, _, ht⟩ := h.2 l u (trans_guard_inv hu); ⟨_, _, trans_guard ht⟩⟩

theorem step_css_guard_l {t : CTree E C X} {t' : CTree F D Y} (h : css L R t t') :
    css L R (.guard t) t' :=
  ⟨fun l t'' ht => h.1 l t'' (trans_guard_inv ht),
   fun l u hu => let ⟨_, _, ht⟩ := h.2 l u hu; ⟨_, _, trans_guard ht⟩⟩

theorem step_css_guard_r {t : CTree E C X} {t' : CTree F D Y} (h : css L R t t') :
    css L R t (.guard t') :=
  ⟨fun l t'' ht => let ⟨l', u', hu, h₁, h₂⟩ := h.1 l t'' ht; ⟨l', u', trans_guard hu, h₁, h₂⟩,
   fun l u hu => h.2 l u (trans_guard_inv hu)⟩

theorem step_css_guard {t : CTree E C X} {t' : CTree F D Y} (h : css L R t t') :
    css L R (.guard t) (.guard t') :=
  step_css_guard_gen h

theorem cssim_guard_l {t : CTree E C X} {t' : CTree F D Y} (h : cssim L t t') :
    cssim L (.guard t) t' :=
  cssim_unfold.2 (step_css_guard_l (cssim_unfold.1 h))

theorem cssim_guard_r {t : CTree E C X} {t' : CTree F D Y} (h : cssim L t t') :
    cssim L t (.guard t') :=
  cssim_unfold.2 (step_css_guard_r (cssim_unfold.1 h))

theorem cssim_guard {t : CTree E C X} {t' : CTree F D Y} (h : cssim L t t') :
    cssim L (.guard t) (.guard t') :=
  cssim_unfold.2 (step_css_guard (cssim_unfold.1 h))

theorem step_css_brS_gen {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (hne : Nonempty (C.O c)) (h : ∀ x, ∃ y, R (k x) (k' y)) (hL : L .tau .tau) :
    css L R (.brS c k) (.brS d k') :=
  step_css_br_gen ⟨Classical.choice hne, _, _, trans_step _⟩ fun x =>
    let ⟨y, hy⟩ := h x; ⟨y, step_css_step_gen hL hy⟩

theorem cssim_brS {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (hne : Nonempty (C.O c)) (h : ∀ x, ∃ y, cssim L (k x) (k' y)) (hL : L .tau .tau) :
    cssim L (.brS c k) (.brS d k') :=
  cssim_br ⟨Classical.choice hne, _, _, trans_step _⟩ fun x =>
    let ⟨y, hy⟩ := h x; ⟨y, cssim_step hy hL⟩

theorem step_css_brS_id_gen {c : C.I} {d : D.I} (hO : C.O c = D.O d) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, R (k x) (k' (cast hO x))) (hL : L .tau .tau) :
    css L R (.brS c k) (.brS d k') :=
  step_css_br_id_gen hO fun x => step_css_step_gen hL (h x)

theorem cssim_brS_id {c : C.I} {d : D.I} (hO : C.O c = D.O d) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, cssim L (k x) (k' (cast hO x))) (hL : L .tau .tau) :
    cssim L (.brS c k) (.brS d k') :=
  cssim_unfold.2 (step_css_brS_id_gen hO h hL)

/-- Visible n-ary spins with nonempty branchings simulate each other completely. -/
theorem cssim_spinS_gen_nonempty {c : C.I} {d : D.I} (x : C.O c) (y : D.O d) (hL : L .tau .tau) :
    cssim L (.spinS_gen c : CTree E C X) (.spinS_gen d : CTree F D Y) :=
  coinduction (b := css L) (fun _ : Unit => (.spinS_gen c : CTree E C X))
    (fun _ => (.spinS_gen d : CTree F D Y)) (by
      intro R _ CIH _
      rw [unfold_spinS_gen c, unfold_spinS_gen d]
      exact step_css_brS_gen ⟨x⟩ (fun _ => ⟨y, CIH ⟨⟩⟩) hL) ⟨⟩

end ProofRules

/-! ## Inversion principles -/

section Inversion
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}

theorem cssim_ret_inv {r₁ : X} {r₂ : Y} (h : cssim L (pure r₁ : CTree E C X) (pure r₂ : CTree F D Y)) :
    L (.val r₁) (.val r₂) := by
  obtain ⟨_, _, hu, -, hl⟩ := (cssim_unfold.1 h).1 _ _ (trans_ret r₁)
  obtain ⟨rfl, rfl⟩ := trans_ret_inv hu
  exact hl

theorem css_ret_l_inv {r : X} {u : CTree F D Y} (h : css L R (pure r) u) :
    ∃ l' u', trans l' u u' ∧ R .stuck u' ∧ L (.val r) l' :=
  h.1 _ _ (trans_ret r)

theorem cssim_ret_l_inv {r : X} {u : CTree F D Y} (h : cssim L (pure r : CTree E C X) u) :
    ∃ l' u', trans l' u u' ∧ L (.val r) l' :=
  let ⟨l', u', hu, _, hl⟩ := css_ret_l_inv (cssim_unfold.1 h); ⟨l', u', hu, hl⟩

theorem cssim_vis_inv_type {e₁ e₂ : E.I} {k₁ : E.O e₁ → CTree E C X} {k₂ : E.O e₂ → CTree E D Y}
    (x₁ : E.O e₁) (h : cssim Eq (.vis e₁ k₁) (.vis e₂ k₂)) : E.O e₁ = E.O e₂ := by
  obtain ⟨_, _, hu, -, hl⟩ := (cssim_unfold.1 h).1 _ _ (trans_vis x₁ k₁)
  obtain ⟨_, -, rfl⟩ := trans_vis_inv hu
  rw [(obs_eq_inv hl).1]

theorem cssbt_vis_inv {e₁ : E.I} {e₂ : F.I} {k₁ : E.O e₁ → CTree E C X}
    {k₂ : F.O e₂ → CTree F D Y} (x : E.O e₁) (h : css L R (.vis e₁ k₁) (.vis e₂ k₂)) :
    (∃ y, L (.obs e₁ x) (.obs e₂ y)) ∧ ∀ x, ∃ y, R (k₁ x) (k₂ y) := by
  refine ⟨?_, fun x => ?_⟩ <;> obtain ⟨_, _, hu, h₁, h₂⟩ := h.1 _ _ (trans_vis x k₁) <;>
    obtain ⟨y, rfl, rfl⟩ := trans_vis_inv hu
  · exact ⟨y, h₂⟩
  · exact ⟨y, h₁⟩

/-- Rocq `ssim_vis_inv` (in `CSSim.v`, about `cssim`); renamed to avoid clashing with `SSim`. -/
theorem cssim_vis_inv {e₁ : E.I} {e₂ : F.I} {k₁ : E.O e₁ → CTree E C X}
    {k₂ : F.O e₂ → CTree F D Y} (x : E.O e₁) (h : cssim L (.vis e₁ k₁) (.vis e₂ k₂)) :
    (∃ y, L (.obs e₁ x) (.obs e₂ y)) ∧ ∀ x, ∃ y, cssim L (k₁ x) (k₂ y) :=
  cssbt_vis_inv x (cssim_unfold.1 h)

theorem css_vis_l_inv {e : E.I} {k : E.O e → CTree E C X} {u : CTree F D Y} (x : E.O e)
    (h : css L R (.vis e k) u) : ∃ l' u', trans l' u u' ∧ R (k x) u' ∧ L (.obs e x) l' :=
  h.1 _ _ (trans_vis x k)

theorem cssim_vis_l_inv {e : E.I} {k : E.O e → CTree E C X} {u : CTree F D Y} (x : E.O e)
    (h : cssim L (.vis e k) u) : ∃ l' u', trans l' u u' ∧ cssim L (k x) u' ∧ L (.obs e x) l' :=
  css_vis_l_inv x (cssim_unfold.1 h)

theorem cssim_brS_inv {c : C.I} {d : D.I} {k₁ : C.O c → CTree E C X} {k₂ : D.O d → CTree F D Y}
    (h : cssim L (.brS c k₁) (.brS d k₂)) : ∀ i₁, ∃ i₂, cssim L (k₁ i₁) (k₂ i₂) := fun i₁ => by
  obtain ⟨_, _, hu, h₁, -⟩ := (cssim_unfold.1 h).1 _ _ (trans_brS k₁ i₁)
  obtain ⟨i₂, rfl, -⟩ := trans_brS_inv hu
  exact ⟨i₂, h₁⟩

theorem css_brS_l_inv {c : C.I} {k : C.O c → CTree E C X} {u : CTree F D Y} (x : C.O c)
    (h : css L R (.brS c k) u) : ∃ l' u', trans l' u u' ∧ R (k x) u' ∧ L .tau l' :=
  h.1 _ _ (trans_brS k x)

theorem cssim_brS_l_inv {c : C.I} {k : C.O c → CTree E C X} {u : CTree F D Y} (x : C.O c)
    (h : cssim L (.brS c k) u) : ∃ l' u', trans l' u u' ∧ cssim L (k x) u' ∧ L .tau l' :=
  css_brS_l_inv x (cssim_unfold.1 h)

theorem css_br_l_inv {c : C.I} {k : C.O c → CTree E C X} {t : CTree F D Y}
    (h : css L R (.br c k) t) (x : C.O c) (hp : ∃ l' t', trans l' (k x) t') : css L R (k x) t :=
  ⟨fun l t' ht => h.1 l t' (trans_br x ht), fun _ _ _ => hp⟩

theorem cssim_br_l_inv {c : C.I} {k : C.O c → CTree E C X} {t : CTree F D Y}
    (h : cssim L (.br c k) t) (x : C.O c) (hp : ∃ l' t', trans l' (k x) t') :
    cssim L (k x) t :=
  cssim_unfold.2 (css_br_l_inv (cssim_unfold.1 h) x hp)

theorem cssim_br_r_inv {d : D.I} {t : CTree E C X} {k : D.O d → CTree F D Y}
    (h : cssim L t (.br d k)) {l : Label E} {t' : CTree E C X} (ht : trans l t t') :
    ∃ l' x t'', trans l' (k x) t'' ∧ L l l' ∧ cssim L t' t'' := by
  obtain ⟨l', u', hu, h₁, h₂⟩ := (cssim_unfold.1 h).1 _ _ ht
  obtain ⟨x, hu⟩ := trans_br_inv hu
  exact ⟨l', x, u', hu, h₂, h₁⟩

end Inversion

end CTree
