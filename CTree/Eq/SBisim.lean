/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.CSSim

/-!
# Strong bisimulation

`sb L` is the strong bisimulation functor: a simulation game played in both directions, labels
related by `L`. `sbisim L` is its greatest fixpoint (← `Eq/SBisim.v`). `CTree` is extensional, so
the Rocq up-to-`equ` closures and `Proper` instances are omitted, and the `Proper (equ eq ==> …) R`
hypotheses of the `step_sb_*_gen` rules are dropped (which makes the `Chain`-specialised variants
`step_sb_*` redundant except for `step_sb_ret`).

Rocq `step` on a goal `sbisim L t u` is `sbisim_unfold.2`; on a hypothesis it is
`sbisim_unfold.1`. Coinduction is the `coinduction R hR CIH` tactic; `step` unfolds `R t u`.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E F C D : Effect.{u}} {X Y X' Y' : Type u}

/-- The strong bisimulation functor. -/
def sb (L : Label E → Label F → Prop) : Mon (Rel (CTree E C X) (CTree F D Y)) where
  body R t u := ss L R t u ∧ ss (flip L) (flip R) u t
  mono h t u H := ⟨(ss L).mono h t u H.1, (ss (flip L)).mono (fun a b => h b a) u t H.2⟩

/-- Strong bisimulation. -/
def sbisim (L : Label E → Label F → Prop) : Rel (CTree E C X) (CTree F D Y) := gfp (sb L)

/-- Strong bisimulation with equal labels. -/
scoped infix:50 " ~ " => sbisim Eq

section Heterogeneous
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem sbisim_unfold : sbisim L t u ↔ sb L (sbisim L) t u :=
  ⟨fun h => gfp_pfp (b := sb L) t u h, fun h => b_chain (gfp_chain (sb L)) t u h⟩

/-- Stuck trees are bisimilar. -/
theorem isStuck_sb (ht : isStuck t) (hu : isStuck u) : sb L R t u :=
  ⟨isStuck_ss ht, isStuck_ss hu⟩

/-- Up-to-`~` on both sides is valid for chain elements of `sb L`. -/
theorem sbisim_clos_sb (hR : Chain (sb L) R) :
    ∀ (t t' : CTree E C X) (u' u : CTree F D Y), t ~ t' → R t' u' → u' ~ u → R t u := by
  refine tower (P := fun R : Rel (CTree E C X) (CTree F D Y) =>
    ∀ t t' u' u, t ~ t' → R t' u' → u' ~ u → R t u) ?_ ?_ R hR
  · intro T hT t t' u' u h₁ h₂ h₃
    exact Rel.inf_apply.2 fun R hR => hT R hR t t' u' u h₁ (Rel.inf_apply.1 h₂ R hR) h₃
  · intro R _ ih t t' u' u h₁ h₂ h₃
    refine ⟨fun l t₁ ht₁ => ?_, fun l u₁ hu₁ => ?_⟩
    · obtain ⟨_, t₁', ht₁', hs₁, rfl⟩ := (sbisim_unfold.1 h₁).1 l t₁ ht₁
      obtain ⟨l', u₁', hu₁', hR', hl⟩ := h₂.1 l t₁' ht₁'
      obtain ⟨_, u₁, hu₁, hs₂, rfl⟩ := (sbisim_unfold.1 h₃).1 l' u₁' hu₁'
      exact ⟨l', u₁, hu₁, ih _ _ _ _ hs₁ hR' hs₂, hl⟩
    · obtain ⟨l₁, u₁', hu₁', hs₂, e₁⟩ := (sbisim_unfold.1 h₃).2 l u₁ hu₁
      obtain ⟨l', t₁', ht₁', hR', hl⟩ := h₂.2 l₁ u₁' hu₁'
      obtain ⟨l₂, t₁, ht₁, hs₁, e₂⟩ := (sbisim_unfold.1 h₁).2 l' t₁' ht₁'
      exact ⟨l₂, t₁, ht₁, ih _ _ _ _ hs₁ hR' hs₂, e₂ ▸ e₁ ▸ hl⟩

theorem sbisim_cssim_subrelation_gen : sbisim L t u → cssim L t u :=
  gfp_mono (b := sb L) (c := css L) (fun _ _ _ h => ⟨h.1, fun l u' hu =>
    let ⟨l', t', h', _⟩ := h.2 l u' hu; ⟨l', t', h'⟩⟩) t u

theorem sbisim_ssim_subrelation_gen : sbisim L t u → ssim L t u :=
  gfp_mono (b := sb L) (c := ss L) (fun _ _ _ h => h.1) t u

/-- `sb` from two simulations. -/
theorem ss_sb (h₁ : ss L R t u) (h₂ : ss (flip L) (flip R) u t) : sb L R t u := ⟨h₁, h₂⟩

end Heterogeneous

section Homogeneous
variable {L : Label E → Label E → Prop} {R : Rel (CTree E C X) (CTree E C X)}

theorem ss_flip (hL : ∀ l l', L l l' → L l' l) {S : Rel (CTree E C X) (CTree E C X)}
    {t u : CTree E C X} (h : ss (flip L) S t u) : ss L S t u := fun l t' ht =>
  let ⟨l', u', h₁, h₂, h₃⟩ := h l t' ht
  ⟨l', u', h₁, h₂, hL _ _ h₃⟩

/-- For symmetric `L`, `sb L` is the symmetrisation of `ss L` (Rocq `sbisim_sym`). -/
theorem sb_symmetrical (hL : ∀ l l', L l l' → L l' l) :
    Symmetrical (converse _) (sb L : Mon (Rel (CTree E C X) (CTree E C X))) (ss L) where
  invol _ := rfl
  eq S := funext fun t => funext fun u => propext <| by
    show sb L S t u ↔ cap (ss L S) (converse _ (ss L (converse _ S))) t u
    rw [Rel.cap_apply]
    exact ⟨fun h => ⟨h.1, ss_flip hL h.2⟩,
      fun h => ⟨h.1, ss_flip (L := flip L) (fun _ _ h => hL _ _ h) (h.2 : ss L (flip S) u t)⟩⟩

theorem sb_chain_refl (hL : ∀ l, L l l) (hR : Chain (sb L) R) : ∀ t, R t t :=
  refl_chain (b := sb L) (fun _ _ ih _ =>
    ⟨fun l t' ht => ⟨l, t', ht, ih t', hL l⟩, fun l t' ht => ⟨l, t', ht, ih t', hL l⟩⟩) R hR

theorem sb_symm (hL : ∀ l l', L l l' → L l' l) (hR : ∀ t u, R t u → R u t) {t u : CTree E C X}
    (h : sb L R t u) : sb L R u t :=
  ⟨fun l u' hu => let ⟨l', t', h₁, h₂, h₃⟩ := h.2 l u' hu; ⟨l', t', h₁, hR _ _ h₂, hL _ _ h₃⟩,
   fun l t' ht => let ⟨l', u', h₁, h₂, h₃⟩ := h.1 l t' ht; ⟨l', u', h₁, hR _ _ h₂, hL _ _ h₃⟩⟩

theorem sb_chain_symm (hL : ∀ l l', L l l' → L l' l) (hR : Chain (sb L) R) :
    ∀ t u, R t u → R u t :=
  symm_symchain (sb_symmetrical hL) R hR

theorem sb_chain_trans (hL : ∀ l₁ l₂ l₃, L l₁ l₂ → L l₂ l₃ → L l₁ l₃) (hR : Chain (sb L) R) :
    ∀ t u v, R t u → R u v → R t v :=
  trans_chain (b := sb L) (fun _ _ ih _ _ _ htu huv =>
    ⟨fun l t' ht =>
      let ⟨l', u', hu, htu', hl⟩ := htu.1 l t' ht
      let ⟨l'', v', hv, huv', hl'⟩ := huv.1 l' u' hu
      ⟨l'', v', hv, ih _ _ _ htu' huv', hL _ _ _ hl hl'⟩,
     fun l v' hv =>
      let ⟨l', u', hu, huv', hl⟩ := huv.2 l v' hv
      let ⟨l'', t', ht, htu', hl'⟩ := htu.2 l' u' hu
      ⟨l'', t', ht, ih _ _ _ htu' huv', hL _ _ _ hl' hl⟩⟩) R hR

theorem sb_chain_equivalence (hL : Equivalence L) (hR : Chain (sb L) R) : Equivalence R :=
  ⟨sb_chain_refl hL.refl hR, sb_chain_symm (L := L) (fun _ _ h => hL.symm h) hR _ _,
   sb_chain_trans (L := L) (fun _ _ _ h₁ h₂ => hL.trans h₁ h₂) hR _ _ _⟩

theorem sbisim_equivalence (hL : Equivalence L) :
    Equivalence (sbisim L : Rel (CTree E C X) (CTree E C X)) :=
  sb_chain_equivalence hL (gfp_chain _)

theorem sbisim_refl (t : CTree E C X) : t ~ t := (sbisim_equivalence ⟨fun _ => rfl, .symm, .trans⟩).refl t
theorem sbisim_symm {t u : CTree E C X} (h : t ~ u) : u ~ t :=
  (sbisim_equivalence ⟨fun _ => rfl, .symm, .trans⟩).symm h
theorem sbisim_trans {t u v : CTree E C X} (h₁ : t ~ u) (h₂ : u ~ v) : t ~ v :=
  (sbisim_equivalence ⟨fun _ => rfl, .symm, .trans⟩).trans h₁ h₂

theorem isStuck_sbisim {t u : CTree E C X} (h : sbisim L t u) (hu : isStuck u) : isStuck t :=
  fun l t' ht => let ⟨_, _, h', _⟩ := (sbisim_unfold.1 h).1 l t' ht; hu _ _ h'

end Homogeneous

/-! ## Up-to `bind` -/

theorem updateValRel_flip {L : Label E → Label F → Prop} {R0 : X → Y → Prop} {l : Label F}
    {l' : Label E} : UpdateValRel (flip L) (flip R0) l l' ↔ UpdateValRel L R0 l' l := by
  constructor <;> rintro (⟨_, _, h⟩ | ⟨_, _, h₁, h₂, h₃⟩)
  · exact .val _ _ h
  · exact .nonval _ _ h₂ h₁ h₃
  · exact .val _ _ h
  · exact .nonval _ _ h₂ h₁ h₃

section Bind
variable {L : Label E → Label F → Prop} {R0 : X → Y → Prop}

/-- One step of the `bind` game: the prefixes play one step of `ss RR S`. -/
theorem ss_bind_step {RR : Label E → Label F → Prop} (hRR : isUpdateValRel L R0 RR)
    {S : Rel (CTree E C X) (CTree F D Y)} {R : Rel (CTree E C X') (CTree F D Y')}
    {t : CTree E C X} {t' : CTree F D Y} {k : X → CTree E C X'} {k' : Y → CTree F D Y'}
    (htt' : ss RR S t t') (hcont : ∀ t₁ t₁', S t₁ t₁' → R (t₁ >>= k) (t₁' >>= k'))
    (hk : ∀ x x', R0 x x' → ss L R (k x) (k' x')) : ss L R (t >>= k) (t' >>= k') := by
  intro l u hu
  rcases trans_bind_inv hu with ⟨hl, t₁, ht₁, rfl⟩ | ⟨x, hx, hk'⟩
  · obtain ⟨l', t₁', ht₁', hss, hll'⟩ := htt' l t₁ ht₁
    obtain ⟨hl', hL⟩ :=
      ((hRR l l' (wfVal_trans ht₁) (wfVal_trans ht₁')).2 hll').nonval_l hl
    exact ⟨l', t₁' >>= k', trans_bind_l hl' ht₁', hcont _ _ hss, hL⟩
  · obtain ⟨l', u', hu', -, hll'⟩ := htt' _ _ hx
    obtain ⟨v₂, rfl, hv⟩ := ((hRR _ _ (wfVal_trans hx) (wfVal_trans hu')).2 hll').val_l
    cases trans_val_inv hu'
    obtain ⟨l'', u'', hu'', hss', hll''⟩ := hk x v₂ hv l u hk'
    exact ⟨l'', u'', trans_bind_r hu' hu'', hss', hll''⟩

/-- Chain elements of `sb L` are closed under `bind` (Rocq `bind_chain_gen`). -/
theorem sb_chain_bind_gen {RR : Label E → Label F → Prop} (hRR : isUpdateValRel L R0 RR)
    {R : Rel (CTree E C X') (CTree F D Y')} (hR : Chain (sb L) R) :
    ∀ (t : CTree E C X) (t' : CTree F D Y) (k : X → CTree E C X') (k' : Y → CTree F D Y'),
      sbisim RR t t' → (∀ x x', R0 x x' → R (k x) (k' x')) → R (t >>= k) (t' >>= k') := by
  have hRR' : isUpdateValRel (flip L) (flip R0) (flip RR) := fun l l' h₁ h₂ =>
    updateValRel_flip.trans (hRR l' l h₂ h₁)
  refine tower (P := fun R : Rel (CTree E C X') (CTree F D Y') => ∀ t t' k k', sbisim RR t t' →
    (∀ x x', R0 x x' → R (k x) (k' x')) → R (t >>= k) (t' >>= k')) ?_ ?_ R hR
  · intro T hT t t' k k' htt' hkk'
    exact Rel.inf_apply.2 fun R hR =>
      hT R hR t t' k k' htt' fun x x' hx => Rel.inf_apply.1 (hkk' x x' hx) R hR
  · intro R hR ih t t' k k' htt' hkk'
    have hk : ∀ x x', R0 x x' → R (k x) (k' x') := fun x x' h => b_chain hR _ _ (hkk' x x' h)
    obtain ⟨h₁, h₂⟩ := sbisim_unfold.1 htt'
    exact ⟨ss_bind_step hRR h₁ (fun a b h => ih a b k k' h hk) fun x x' h => (hkk' x x' h).1,
      ss_bind_step hRR' h₂ (fun a b h => ih b a k k' h hk) fun x' x h => (hkk' x x' h).2⟩

theorem sbisim_clo_bind_gen {L0 : Label E → Label F → Prop} (hL0 : isUpdateValRel L R0 L0)
    {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'} {k₂ : Y → CTree F D Y'}
    (h₁ : sbisim L0 t₁ t₂) (h₂ : ∀ x y, R0 x y → sbisim L (k₁ x) (k₂ y)) :
    sbisim L (t₁ >>= k₁) (t₂ >>= k₂) :=
  sb_chain_bind_gen hL0 (gfp_chain _) _ _ _ _ h₁ h₂

theorem sbisim_clo_bind {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'}
    {k₂ : Y → CTree F D Y'} (h₁ : sbisim (UpdateValRel L R0) t₁ t₂)
    (h₂ : ∀ x y, R0 x y → sbisim L (k₁ x) (k₂ y)) : sbisim L (t₁ >>= k₁) (t₂ >>= k₂) :=
  sbisim_clo_bind_gen updateValRel_correct h₁ h₂

theorem sb_chain_bind {R : Rel (CTree E C X') (CTree F D Y')} (hR : Chain (sb L) R)
    {t : CTree E C X} {t' : CTree F D Y} {k : X → CTree E C X'} {k' : Y → CTree F D Y'}
    (h₁ : sbisim (UpdateValRel L R0) t t') (h₂ : ∀ x x', R0 x x' → R (k x) (k' x')) :
    R (t >>= k) (t' >>= k') :=
  sb_chain_bind_gen updateValRel_correct hR _ _ _ _ h₁ h₂

end Bind

theorem sb_clo_bind_eq {R : Rel (CTree E C Y) (CTree E C Y)} (hR : Chain (sb Eq) R)
    {t₁ t₂ : CTree E C X} {k₁ k₂ : X → CTree E C Y} (h₁ : t₁ ~ t₂) (h₂ : ∀ x, R (k₁ x) (k₂ x)) :
    R (t₁ >>= k₁) (t₂ >>= k₂) :=
  sb_chain_bind_gen (R0 := Eq) updateValRel_eq hR _ _ _ _ h₁ (by rintro x _ rfl; exact h₂ x)

theorem sbisim_clo_bind_eq {t₁ : CTree E C X} {t₂ : CTree E D X} {k₁ : X → CTree E C X'}
    {k₂ : X → CTree E D X'} (h₁ : t₁ ~ t₂) (h₂ : ∀ x, k₁ x ~ k₂ x) : t₁ >>= k₁ ~ t₂ >>= k₂ :=
  sbisim_clo_bind_gen (R0 := Eq) updateValRel_eq h₁ (by rintro x _ rfl; exact h₂ x)

theorem sbisim_bind_eq (t : CTree E C X) {k₁ k₂ : X → CTree E C X'} (h : ∀ x, k₁ x ~ k₂ x) :
    t >>= k₁ ~ t >>= k₂ :=
  sbisim_clo_bind_eq (sbisim_refl t) h

theorem sb_chain_bind_eq {R : Rel (CTree E C Y) (CTree E C Y)} (hR : Chain (sb Eq) R)
    (t : CTree E C X) {k₁ k₂ : X → CTree E C Y} (h : ∀ x, R (k₁ x) (k₂ x)) :
    R (t >>= k₁) (t >>= k₂) :=
  sb_clo_bind_eq hR (sbisim_refl t) h

theorem vis_chain_gen {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}
    (hR : Chain (sb L) R) (e : E.I) (e' : F.I) (k : E.O e → CTree E C X)
    (k' : F.O e' → CTree F D Y) (right : E.O e → F.O e') (left : F.O e' → E.O e)
    (h₁ : ∀ x, L (.obs e x) (.obs e' (right x))) (h₂ : ∀ y, L (.obs e (left y)) (.obs e' y))
    (h₃ : ∀ x, R (k x) (k' (right x))) (h₄ : ∀ y, R (k (left y)) (k' y)) :
    R (.vis e k) (.vis e' k') :=
  b_chain hR _ _
    ⟨fun _ _ ht => by
      obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
      exact ⟨_, _, trans_vis (right x) k', h₃ x, h₁ x⟩,
     fun _ _ hu => by
      obtain ⟨y, rfl, rfl⟩ := trans_vis_inv hu
      exact ⟨_, _, trans_vis (left y) k, h₄ y, h₂ y⟩⟩

theorem vis_chain {R : Rel (CTree E C X) (CTree E C X)} (hR : Chain (sb Eq) R) (e : E.I)
    {k k' : E.O e → CTree E C X} (h : ∀ x, R (k x) (k' x)) : R (.vis e k) (.vis e k') :=
  vis_chain_gen hR e e k k' id id (fun _ => rfl) (fun _ => rfl) h h

/-! ## Proof rules for `sbisim` -/

section ProofRules
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}

theorem step_sb_ret_gen {x : X} {y : Y} (hR : R .stuck .stuck) (hL : L (.val x) (.val y)) :
    sb L R (pure x) (pure y) :=
  ⟨fun _ _ ht => by
    obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    exact ⟨_, _, trans_ret y, hR, hL⟩,
   fun _ _ hu => by
    obtain ⟨rfl, rfl⟩ := trans_ret_inv hu
    exact ⟨_, _, trans_ret x, hR, hL⟩⟩

theorem step_sb_ret {x : X} {y : Y} (hR : Chain (sb L) R) (hL : L (.val x) (.val y)) :
    sb L R (pure x) (pure y) :=
  step_sb_ret_gen (b_chain hR _ _ (isStuck_sb stuck_isStuck stuck_isStuck)) hL

theorem sbisim_ret {x : X} {y : Y} (hL : L (.val x) (.val y)) :
    sbisim L (pure x : CTree E C X) (pure y : CTree F D Y) :=
  sbisim_unfold.2 (step_sb_ret (gfp_chain _) hL)

theorem step_sb_vis_gen (e : E.I) (f : F.I) (k : E.O e → CTree E C X) (k' : F.O f → CTree F D Y)
    (h₁ : ∀ x, ∃ y, R (k x) (k' y) ∧ L (.obs e x) (.obs f y))
    (h₂ : ∀ y, ∃ x, R (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    sb L R (.vis e k) (.vis f k') :=
  ⟨fun _ _ ht => by
    obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
    obtain ⟨y, h, hl⟩ := h₁ x
    exact ⟨_, _, trans_vis y k', h, hl⟩,
   fun _ _ hu => by
    obtain ⟨y, rfl, rfl⟩ := trans_vis_inv hu
    obtain ⟨x, h, hl⟩ := h₂ y
    exact ⟨_, _, trans_vis x k, h, hl⟩⟩

theorem sbisim_vis (e : E.I) (f : F.I) (k : E.O e → CTree E C X) (k' : F.O f → CTree F D Y)
    (h₁ : ∀ x, ∃ y, sbisim L (k x) (k' y) ∧ L (.obs e x) (.obs f y))
    (h₂ : ∀ y, ∃ x, sbisim L (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    sbisim L (.vis e k) (.vis f k') :=
  sbisim_unfold.2 (step_sb_vis_gen e f k k' h₁ h₂)

/-- The Rocq version takes `e : E X'`, `f : F X'` with a common answer type; here both sides use
the same event. -/
theorem step_sb_vis_id_gen {L : Label E → Label E → Prop} {R : Rel (CTree E C X) (CTree E D Y)}
    (e : E.I) (k : E.O e → CTree E C X) (k' : E.O e → CTree E D Y)
    (h : ∀ x, R (k x) (k' x) ∧ L (.obs e x) (.obs e x)) : sb L R (.vis e k) (.vis e k') :=
  step_sb_vis_gen e e k k' (fun x => ⟨x, h x⟩) (fun x => ⟨x, h x⟩)

theorem sbisim_vis_id {L : Label E → Label E → Prop} (e : E.I) (k : E.O e → CTree E C X)
    (k' : E.O e → CTree E D Y) (h : ∀ x, sbisim L (k x) (k' x) ∧ L (.obs e x) (.obs e x)) :
    sbisim L (.vis e k) (.vis e k') :=
  sbisim_unfold.2 (step_sb_vis_id_gen e k k' h)

/-! Guard -/

section Guard
variable {t : CTree E C X} {u : CTree F D Y}

theorem step_sb_guard_l_gen (h : sb L R t u) : sb L R (.guard t) u :=
  ⟨fun l t' ht => h.1 l t' (trans_guard_inv ht),
   fun l u' hu => let ⟨l', t', h₁, h₂, h₃⟩ := h.2 l u' hu; ⟨l', t', trans_guard h₁, h₂, h₃⟩⟩

theorem step_sb_guard_r_gen (h : sb L R t u) : sb L R t (.guard u) :=
  ⟨fun l t' ht => let ⟨l', u', h₁, h₂, h₃⟩ := h.1 l t' ht; ⟨l', u', trans_guard h₁, h₂, h₃⟩,
   fun l u' hu => h.2 l u' (trans_guard_inv hu)⟩

theorem step_sb_guard_gen (h : sb L R t u) : sb L R (.guard t) (.guard u) :=
  step_sb_guard_l_gen (step_sb_guard_r_gen h)

theorem sbisim_guard (h : sbisim L t u) : sbisim L (.guard t) (.guard u) :=
  sbisim_unfold.2 (step_sb_guard_gen (sbisim_unfold.1 h))

theorem sbisim_guard_l (h : sbisim L t u) : sbisim L (.guard t) u :=
  sbisim_unfold.2 (step_sb_guard_l_gen (sbisim_unfold.1 h))

theorem sbisim_guard_r (h : sbisim L t u) : sbisim L t (.guard u) :=
  sbisim_unfold.2 (step_sb_guard_r_gen (sbisim_unfold.1 h))

end Guard

/-! Br -/

theorem step_sb_br_gen (c : C.I) (d : D.I) (k : C.O c → CTree E C X) (k' : D.O d → CTree F D Y)
    (h₁ : ∀ x, ∃ y, sb L R (k x) (k' y)) (h₂ : ∀ y, ∃ x, sb L R (k x) (k' y)) :
    sb L R (.br c k) (.br d k') :=
  ⟨fun l t' ht =>
    let ⟨x, ht⟩ := trans_br_inv ht
    let ⟨y, h⟩ := h₁ x
    let ⟨l', u', h₁, h₂, h₃⟩ := h.1 l t' ht
    ⟨l', u', trans_br y h₁, h₂, h₃⟩,
   fun l u' hu =>
    let ⟨y, hu⟩ := trans_br_inv hu
    let ⟨x, h⟩ := h₂ y
    let ⟨l', t', h₁, h₂, h₃⟩ := h.2 l u' hu
    ⟨l', t', trans_br x h₁, h₂, h₃⟩⟩

/-- The Rocq version takes `c : C X'`, `d : D X'` with a common arity; here both sides branch on
the same `c`. -/
theorem step_sb_br_id_gen {R : Rel (CTree E C X) (CTree F C Y)} (c : C.I)
    (k : C.O c → CTree E C X) (k' : C.O c → CTree F C Y) (h : ∀ x, sb L R (k x) (k' x)) :
    sb L R (.br c k) (.br c k') :=
  step_sb_br_gen c c k k' (fun x => ⟨x, h x⟩) (fun x => ⟨x, h x⟩)

theorem step_sb_br_l_gen (c : C.I) (k : C.O c → CTree E C X) (u : CTree F D Y) (x : C.O c)
    (h : ∀ x, sb L R (k x) u) : sb L R (.br c k) u :=
  ⟨fun l t' ht => let ⟨n, ht⟩ := trans_br_inv ht; (h n).1 l t' ht,
   fun l u' hu => let ⟨l', t', h₁, h₂, h₃⟩ := (h x).2 l u' hu; ⟨l', t', trans_br x h₁, h₂, h₃⟩⟩

theorem step_sb_br_r_gen (d : D.I) (t : CTree E C X) (k : D.O d → CTree F D Y) (y : D.O d)
    (h : ∀ y, sb L R t (k y)) : sb L R t (.br d k) :=
  ⟨fun l t' ht => let ⟨l', u', h₁, h₂, h₃⟩ := (h y).1 l t' ht; ⟨l', u', trans_br y h₁, h₂, h₃⟩,
   fun l u' hu => let ⟨n, hu⟩ := trans_br_inv hu; (h n).2 l u' hu⟩

theorem sbisim_br (c : C.I) (d : D.I) (k : C.O c → CTree E C X) (k' : D.O d → CTree F D Y)
    (h₁ : ∀ x, ∃ y, sbisim L (k x) (k' y)) (h₂ : ∀ y, ∃ x, sbisim L (k x) (k' y)) :
    sbisim L (.br c k) (.br d k') :=
  sbisim_unfold.2 <| step_sb_br_gen c d k k'
    (fun x => let ⟨y, h⟩ := h₁ x; ⟨y, sbisim_unfold.1 h⟩)
    (fun y => let ⟨x, h⟩ := h₂ y; ⟨x, sbisim_unfold.1 h⟩)

theorem sbisim_br_id (c : C.I) (k : C.O c → CTree E C X) (k' : C.O c → CTree F C Y)
    (h : ∀ x, sbisim L (k x) (k' x)) : sbisim L (.br c k) (.br c k') :=
  sbisim_unfold.2 (step_sb_br_id_gen c k k' fun x => sbisim_unfold.1 (h x))

theorem sbisim_br_l (c : C.I) (k : C.O c → CTree E C X) (u : CTree F D Y) (x : C.O c)
    (h : ∀ x, sbisim L (k x) u) : sbisim L (.br c k) u :=
  sbisim_unfold.2 (step_sb_br_l_gen c k u x fun x => sbisim_unfold.1 (h x))

theorem sbisim_br_r (d : D.I) (t : CTree E C X) (k : D.O d → CTree F D Y) (y : D.O d)
    (h : ∀ y, sbisim L t (k y)) : sbisim L t (.br d k) :=
  sbisim_unfold.2 (step_sb_br_r_gen d t k y fun y => sbisim_unfold.1 (h y))

/-! Step -/

theorem step_sb_step_gen {t : CTree E C X} {u : CTree F D Y} (hL : L .tau .tau) (h : R t u) :
    sb L R (.step t) (.step u) :=
  ⟨fun _ _ ht => by
    obtain ⟨rfl, rfl⟩ := trans_step_inv ht
    exact ⟨_, _, trans_step u, h, hL⟩,
   fun _ _ hu => by
    obtain ⟨rfl, rfl⟩ := trans_step_inv hu
    exact ⟨_, _, trans_step t, h, hL⟩⟩

theorem sbisim_step {t : CTree E C X} {u : CTree F D Y} (hL : L .tau .tau) (h : sbisim L t u) :
    sbisim L (.step t) (.step u) :=
  sbisim_unfold.2 (step_sb_step_gen hL h)

/-! BrS -/

theorem step_sb_brS_gen (c : C.I) (d : D.I) (k : C.O c → CTree E C X) (k' : D.O d → CTree F D Y)
    (hL : L .tau .tau) (h₁ : ∀ x, ∃ y, R (k x) (k' y)) (h₂ : ∀ y, ∃ x, R (k x) (k' y)) :
    sb L R (.brS c k) (.brS d k') :=
  step_sb_br_gen c d _ _ (fun x => let ⟨y, h⟩ := h₁ x; ⟨y, step_sb_step_gen hL h⟩)
    (fun y => let ⟨x, h⟩ := h₂ y; ⟨x, step_sb_step_gen hL h⟩)

theorem step_sb_brS_id_gen {R : Rel (CTree E C X) (CTree F C Y)} (c : C.I)
    (k : C.O c → CTree E C X) (k' : C.O c → CTree F C Y) (hL : L .tau .tau)
    (h : ∀ x, R (k x) (k' x)) : sb L R (.brS c k) (.brS c k') :=
  step_sb_br_id_gen c _ _ fun x => step_sb_step_gen hL (h x)

theorem sbisim_brS (c : C.I) (d : D.I) (k : C.O c → CTree E C X) (k' : D.O d → CTree F D Y)
    (hL : L .tau .tau) (h₁ : ∀ x, ∃ y, sbisim L (k x) (k' y))
    (h₂ : ∀ y, ∃ x, sbisim L (k x) (k' y)) : sbisim L (.brS c k) (.brS d k') :=
  sbisim_unfold.2 (step_sb_brS_gen c d k k' hL h₁ h₂)

theorem sbisim_brS_id (c : C.I) (k : C.O c → CTree E C X) (k' : C.O c → CTree F C Y)
    (hL : L .tau .tau) (h : ∀ x, sbisim L (k x) (k' x)) : sbisim L (.brS c k) (.brS c k') :=
  sbisim_unfold.2 (step_sb_brS_id_gen c k k' hL h)

end ProofRules

/-! ## Proof system for `~` -/

section SbProofSystem

theorem sb_ret {x y : X} (h : x = y) : (pure x : CTree E C X) ~ (pure y : CTree E C X) :=
  sbisim_ret (by subst h; rfl)

theorem sb_vis (e : E.I) {k k' : E.O e → CTree E C Y} (h : ∀ x, k x ~ k' x) :
    CTree.vis e k ~ .vis e k' :=
  vis_chain (gfp_chain _) e h

/-- Invisible guards can be stripped out, visible steps cannot. -/
theorem sb_guard (t : CTree E C X) : CTree.guard t ~ t := sbisim_guard_l (sbisim_refl t)

theorem sb_guard_l {t u : CTree E C X} (h : t ~ u) : CTree.guard t ~ u := sbisim_guard_l h
theorem sb_guard_r {t u : CTree E C X} (h : t ~ u) : t ~ CTree.guard u := sbisim_guard_r h
theorem sb_guard_lr {t u : CTree E C X} (h : t ~ u) : CTree.guard t ~ .guard u := sbisim_guard h
theorem sb_step {t u : CTree E C X} (h : t ~ u) : CTree.step t ~ .step u := sbisim_step rfl h

theorem sb_br (ci cj : C.I) (k : C.O ci → CTree E C X) (k' : C.O cj → CTree E C X)
    (h₁ : ∀ x, ∃ y, k x ~ k' y) (h₂ : ∀ y, ∃ x, k x ~ k' y) : CTree.br ci k ~ .br cj k' :=
  sbisim_br ci cj k k' h₁ h₂

theorem sb_br_id (c : C.I) (k k' : C.O c → CTree E C X) (h : ∀ x, k x ~ k' x) :
    CTree.br c k ~ .br c k' :=
  sbisim_br_id c k k' h

theorem sb_br_l (c : C.I) (y : C.O c) (k : C.O c → CTree E C X) (t : CTree E C X)
    (h : ∀ x, k x ~ t) : CTree.br c k ~ t :=
  sbisim_br_l c k t y h

theorem sb_brS (ci cj : C.I) (k : C.O ci → CTree E C X) (k' : C.O cj → CTree E C X)
    (h₁ : ∀ x, ∃ y, k x ~ k' y) (h₂ : ∀ y, ∃ x, k x ~ k' y) : CTree.brS ci k ~ .brS cj k' :=
  sbisim_brS ci cj k k' rfl h₁ h₂

theorem sb_brS_id (c : C.I) (k k' : C.O c → CTree E C X) (h : ∀ x, k x ~ k' x) :
    CTree.brS c k ~ .brS c k' :=
  sbisim_brS_id c k k' rfl h

theorem sb_unfold_forever (k : X → CTree E C X) (i : X) :
    CTree.forever k i ~ k i >>= CTree.forever k := by
  rw [unfold_forever]
  exact sbisim_bind_eq _ fun x => sb_guard _

end SbProofSystem

/-! ## Sanity checks and inversions -/

section WithParams

theorem sbisim_spinS_gen_nonempty (c c' : C.I) (x : C.O c) (y : C.O c') :
    (CTree.spinS_gen c : CTree E C X) ~ (.spinS_gen c' : CTree E C X) := by
  coinduction _ _ CIH
  rw [unfold_spinS_gen c, unfold_spinS_gen c']
  exact step_sb_brS_gen c c' _ _ rfl (fun _ => ⟨y, CIH⟩) fun _ => ⟨x, CIH⟩

theorem spin_gen_bisim (c c' : C.I) :
    (CTree.spin_gen c : CTree E C X) ~ (.spin_gen c' : CTree E C X) :=
  sbisim_unfold.2 (isStuck_sb (spin_gen_isStuck c) (spin_gen_isStuck c'))

/-- Trees with the same transitions are bisimilar. -/
theorem sbisim_of_trans_iff {t u : CTree E C X} (h : ∀ l t', trans l t t' ↔ trans l u t') :
    t ~ u :=
  sbisim_unfold.2 ⟨fun l t' ht => ⟨l, t', (h l t').1 ht, sbisim_refl t', rfl⟩,
    fun l t' ht => ⟨l, t', (h l t').2 ht, sbisim_refl t', rfl⟩⟩

section Br2
variable [B2 -< C] [LawfulSubeffect B2 C] {l : Label E} {t u v t' : CTree E C X}

theorem trans_br2_iff : trans l (CTree.br2 t u) t' ↔ trans l t t' ∨ trans l u t' :=
  ⟨trans_br2_inv, fun h => h.elim trans_br2_l trans_br2_r⟩

theorem trans_brS2_iff : trans l (CTree.brS2 t u) t' ↔ l = .tau ∧ (t' = t ∨ t' = u) :=
  ⟨trans_brS2_inv, by rintro ⟨rfl, rfl | rfl⟩; exact trans_brS2_l; exact trans_brS2_r⟩

/-! `br2` is associative, commutative, idempotent, merges into `br3`, and admits stuck units. -/

theorem br2_assoc (t u v : CTree E C X) : CTree.br2 (.br2 t u) v ~ .br2 t (.br2 u v) :=
  sbisim_of_trans_iff fun _ _ => by simp only [trans_br2_iff, or_assoc]

theorem br2_commut (t u : CTree E C X) : CTree.br2 t u ~ .br2 u t :=
  sbisim_of_trans_iff fun _ _ => by simp only [trans_br2_iff, or_comm]

theorem br2_idem (t : CTree E C X) : CTree.br2 t t ~ t :=
  sbisim_of_trans_iff fun _ _ => by simp only [trans_br2_iff, or_self]

theorem br2_merge [B3 -< C] [LawfulSubeffect B3 C] (t u v : CTree E C X) :
    CTree.br2 (.br2 t u) v ~ .br3 t u v :=
  sbisim_of_trans_iff fun _ _ => by
    simp only [trans_br2_iff, or_assoc]
    exact ⟨fun h => h.elim trans_br3_1 (·.elim trans_br3_2 trans_br3_3), trans_br3_inv⟩

theorem br2_isStuck (h : isStuck u) (v : CTree E C X) : CTree.br2 u v ~ v :=
  sbisim_of_trans_iff fun _ _ => by
    rw [trans_br2_iff]; exact ⟨(·.resolve_left (h _ _)), .inr⟩

theorem br2_stuck_l (t : CTree E C X) : CTree.br2 .stuck t ~ t := br2_isStuck stuck_isStuck t
theorem br2_stuck_r (t : CTree E C X) : CTree.br2 t .stuck ~ t :=
  sbisim_trans (br2_commut _ _) (br2_stuck_l t)
theorem br2_spin_l (t : CTree E C X) : CTree.br2 .spin t ~ t := br2_isStuck spin_isStuck t
theorem br2_spin_r (t : CTree E C X) : CTree.br2 t .spin ~ t :=
  sbisim_trans (br2_commut _ _) (br2_spin_l t)

/-! `brS2` is commutative and "almost" idempotent. -/

theorem brS2_commut (t u : CTree E C X) : CTree.brS2 t u ~ .brS2 u t :=
  sbisim_of_trans_iff fun _ _ => by simp only [trans_brS2_iff, or_comm]

theorem brS2_idem (t : CTree E C X) : CTree.brS2 t t ~ .step t :=
  sbisim_of_trans_iff fun _ _ => by
    rw [trans_brS2_iff, or_self]
    exact ⟨fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ trans_step t, fun h => (trans_step_inv h).symm⟩

end Br2

theorem sbisim_ret_inv {r₁ r₂ : X} (h : (pure r₁ : CTree E C X) ~ (pure r₂ : CTree E C X)) :
    r₁ = r₂ := by
  obtain ⟨_, _, ht, -, rfl⟩ := (sbisim_unfold.1 h).1 _ _ (trans_ret r₁)
  exact val_eq_inv (trans_ret_inv ht).2

/-- Rocq `sbisim_vis_invT` concludes equality of the answer types; in Lean the events themselves
are equal. Needs an answer to the left event to take a step. -/
theorem sbisim_vis_invT {e₁ e₂ : E.I} {k₁ : E.O e₁ → CTree E C X} {k₂ : E.O e₂ → CTree E C X}
    (x : E.O e₁) (h : CTree.vis e₁ k₁ ~ .vis e₂ k₂) : e₁ = e₂ := by
  obtain ⟨_, _, ht, -, rfl⟩ := (sbisim_unfold.1 h).1 _ _ (trans_vis x k₁)
  obtain ⟨_, -, hl⟩ := trans_vis_inv ht
  exact (obs_eq_inv hl).1

theorem sbisim_vis_inv {e : E.I} {k₁ k₂ : E.O e → CTree E C X} (h : CTree.vis e k₁ ~ .vis e k₂) :
    ∀ x, k₁ x ~ k₂ x := by
  intro x
  obtain ⟨_, _, ht, hs, rfl⟩ := (sbisim_unfold.1 h).1 _ _ (trans_vis x k₁)
  obtain ⟨y, rfl, hl⟩ := trans_vis_inv ht
  cases eq_of_heq (obs_eq_inv hl).2
  exact hs

theorem sbisim_brS_inv {c₁ c₂ : C.I} {k₁ : C.O c₁ → CTree E C X} {k₂ : C.O c₂ → CTree E C X}
    (h : CTree.brS c₁ k₁ ~ .brS c₂ k₂) :
    (∀ i₁, ∃ i₂, k₁ i₁ ~ k₂ i₂) ∧ (∀ i₂, ∃ i₁, k₁ i₁ ~ k₂ i₂) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · obtain ⟨_, _, ht, hs, -⟩ := (sbisim_unfold.1 h).1 _ _ (trans_brS k₁ i)
    obtain ⟨n, rfl, -⟩ := trans_brS_inv ht
    exact ⟨n, hs⟩
  · obtain ⟨_, _, ht, hs, -⟩ := (sbisim_unfold.1 h).2 _ _ (trans_brS k₂ i)
    obtain ⟨n, rfl, -⟩ := trans_brS_inv ht
    exact ⟨n, hs⟩

/-- Head constructors that can never be bisimilar. `vis e k ~ stuck` holds when `e` has no
answers, so that case requires an inhabitant. -/
def areBisimIncompat (t u : CTree E C X) : Prop :=
  match t.unfold, u.unfold with
  | .br .., _ | _, .br .. | .guard _, _ | _, .guard _ => False
  | .ret _, .ret _ | .vis .., .vis .. | .step _, .step _ | .stuck, .stuck => False
  | .vis e _, .stuck | .stuck, .vis e _ => Nonempty (E.O e)
  | _, _ => True

theorem sbisim_trans_l {l : Label E} {t t' u : CTree E C X} (h : t ~ u) (ht : trans l t t') :
    ∃ u', trans l u u' :=
  let ⟨_, u', hu, _, hl⟩ := (sbisim_unfold.1 h).1 l t' ht; ⟨u', hl ▸ hu⟩

theorem sbisim_trans_r {l : Label E} {t u u' : CTree E C X} (h : t ~ u) (hu : trans l u u') :
    ∃ t', trans l t t' :=
  let ⟨_, t', ht, _, hl⟩ := (sbisim_unfold.1 h).2 l u' hu; ⟨t', hl ▸ ht⟩

/-- `t` can emit a label of kind `l`, which `u` cannot. -/
local macro "sb_inv " h:ident : tactic => `(tactic| first
  | exact (trans_stuck_inv $h).elim
  | (have := (trans_step_inv $h).2; cases this)
  | (have := (trans_ret_inv $h).2; cases this)
  | (obtain ⟨_, -, h''⟩ := trans_vis_inv $h; cases h''))

theorem sbisim_absurd {t u : CTree E C X} (hi : areBisimIncompat t u) (h : t ~ u) : False := by
  cases t <;> cases u <;> simp [areBisimIncompat] at hi
  all_goals first
    | (obtain ⟨_, h'⟩ := sbisim_trans_l h (trans_ret _); sb_inv h'; done)
    | (obtain ⟨_, h'⟩ := sbisim_trans_r h (trans_ret _); sb_inv h'; done)
    | (obtain ⟨_, h'⟩ := sbisim_trans_l h (trans_step _); sb_inv h'; done)
    | (obtain ⟨_, h'⟩ := sbisim_trans_r h (trans_step _); sb_inv h'; done)
    | (obtain ⟨x⟩ := hi; obtain ⟨_, h'⟩ := sbisim_trans_l h (trans_vis x _); sb_inv h'; done)
    | (obtain ⟨x⟩ := hi; obtain ⟨_, h'⟩ := sbisim_trans_r h (trans_vis x _); sb_inv h'; done)

theorem sbisim_ret_vis_inv {r : X} {e : E.I} {k : E.O e → CTree E C X}
    (h : (pure r : CTree E C X) ~ .vis e k) : False :=
  sbisim_absurd (by simp [areBisimIncompat]) h

theorem sbisim_ret_BrS_inv {r : X} {c : C.I} {k : C.O c → CTree E C X}
    (h : (pure r : CTree E C X) ~ .brS c k) : False := by
  obtain ⟨_, h'⟩ := sbisim_trans_l h (trans_ret r)
  obtain ⟨_, -, h''⟩ := trans_brS_inv h'
  cases h''

/-- Needs an inhabitant of the branch arity. -/
theorem sbisim_vis_BrS_inv {e : E.I} {k₁ : E.O e → CTree E C X} {c : C.I}
    {k₂ : C.O c → CTree E C X} (y : C.O c) (h : CTree.vis e k₁ ~ .brS c k₂) : False := by
  obtain ⟨_, h'⟩ := sbisim_trans_r h (trans_brS k₂ y)
  sb_inv h'

/-- Needs an answer to the event. -/
theorem sbisim_vis_BrS_inv' {e : E.I} {k₁ : E.O e → CTree E C X} {c : C.I}
    {k₂ : C.O c → CTree E C X} (x : E.O e) (h : CTree.vis e k₁ ~ .brS c k₂) : False := by
  obtain ⟨_, h'⟩ := sbisim_trans_l h (trans_vis x k₁)
  obtain ⟨_, -, h''⟩ := trans_brS_inv h'
  cases h''

theorem sbisim_ret_Br_inv {r : X} {c : C.I} {k : C.O c → CTree E C X}
    (h : (pure r : CTree E C X) ~ .br c k) : ∃ x, (pure r : CTree E C X) ~ k x := by
  obtain ⟨_, u', hu, hs, rfl⟩ := (sbisim_unfold.1 h).1 _ _ (trans_ret r)
  obtain ⟨x, hu⟩ := trans_br_inv hu
  refine ⟨x, sbisim_unfold.2 ⟨fun _ _ ht => ?_, fun l u'' hu' => ?_⟩⟩
  · obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    exact ⟨_, u', hu, hs, rfl⟩
  · exact (sbisim_unfold.1 h).2 l u'' (trans_br x hu')

end WithParams

/-! ## Strong simulations -/

section StrongSimulations

theorem sbisim_clos_ss {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}
    (hR : Chain (ss L) R) :
    ∀ (t t' : CTree E C X) (u' u : CTree F D Y), t ~ t' → R t' u' → u' ~ u → R t u := by
  refine tower (P := fun R : Rel (CTree E C X) (CTree F D Y) =>
    ∀ t t' u' u, t ~ t' → R t' u' → u' ~ u → R t u) ?_ ?_ R hR
  · intro T hT t t' u' u h₁ h₂ h₃
    exact Rel.inf_apply.2 fun R hR => hT R hR t t' u' u h₁ (Rel.inf_apply.1 h₂ R hR) h₃
  · intro R _ ih t t' u' u h₁ h₂ h₃ l t₁ ht₁
    obtain ⟨_, t₁', ht₁', hs₁, rfl⟩ := (sbisim_unfold.1 h₁).1 l t₁ ht₁
    obtain ⟨l', u₁', hu₁', hR', hl⟩ := h₂ l t₁' ht₁'
    obtain ⟨_, u₁, hu₁, hs₂, rfl⟩ := (sbisim_unfold.1 h₃).1 l' u₁' hu₁'
    exact ⟨l', u₁, hu₁, ih _ _ _ _ hs₁ hR' hs₂, hl⟩

/-- Rewriting `~` on both sides of `ssim L` (the Rocq `sbisim_eq_clos_ssim_*` instances). -/
theorem sbisim_clos_ssim {L : Label E → Label F → Prop} {t t' : CTree E C X}
    {u' u : CTree F D Y} (h₁ : t ~ t') (h₂ : ssim L t' u') (h₃ : u' ~ u) : ssim L t u :=
  sbisim_clos_ss (gfp_chain _) t t' u' u h₁ h₂ h₃

theorem split_sb_eq {RR : Rel (CTree E C X) (CTree E C X)} {t t' : CTree E C X}
    (h₁ : ss Eq RR t t') (h₂ : ss Eq (flip RR) t' t) : sb Eq RR t t' :=
  ⟨h₁, fun l u hu => let ⟨l', t'', a, b, c⟩ := h₂ l u hu; ⟨l', t'', a, b, c.symm⟩⟩

theorem split_sbisim_eq {t u : CTree E C X} :
    t ~ u ↔ ss Eq (sbisim Eq) t u ∧ ss Eq (sbisim Eq) u t :=
  ⟨fun h => ⟨(sbisim_unfold.1 h).1, (sbisim_unfold.1 (sbisim_symm h)).1⟩, fun h =>
    sbisim_unfold.2 (split_sb_eq h.1 fun l v hv =>
      let ⟨l', t', a, b, c⟩ := h.2 l v hv; ⟨l', t', a, sbisim_symm b, c⟩)⟩

/-- Two strong simulations do not make a bisimulation: `step (pure ⟨⟩)` and
`brS2 (pure ⟨⟩) stuck` simulate each other but are not bisimilar. -/
theorem ssim_sbisim_nequiv :
    let t₁ : CTree E B2 PUnit := .step (pure ⟨⟩)
    let t₂ : CTree E B2 PUnit := .brS2 (pure ⟨⟩) .stuck
    ssim Eq t₁ t₂ ∧ ssim Eq t₂ t₁ ∧ ¬ sbisim Eq t₁ t₂ := by
  refine ⟨ssim_unfold.2 fun _ _ ht => ?_, ssim_unfold.2 fun _ _ ht => ?_, fun h => ?_⟩
  · obtain ⟨rfl, rfl⟩ := trans_step_inv ht
    exact ⟨_, _, trans_brS2_l, ssim_refl (fun _ => rfl) _, rfl⟩
  · obtain ⟨rfl, rfl | rfl⟩ := trans_brS2_inv ht
    · exact ⟨_, _, trans_step _, ssim_refl (fun _ => rfl) _, rfl⟩
    · exact ⟨_, _, trans_step _, stuck_ssim, rfl⟩
  · obtain ⟨_, _, ht, hs, -⟩ := (sbisim_unfold.1 h).2 _ _ trans_brS2_r
    obtain ⟨rfl, -⟩ := trans_step_inv ht
    obtain ⟨_, _, hu, -⟩ := (sbisim_unfold.1 hs).1 _ _ (trans_ret _)
    exact trans_stuck_inv hu

end StrongSimulations

/-! ## Complete strong simulations -/

section CompleteStrongSimulations
variable {L : Label E → Label F → Prop} {RR : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {t' : CTree F D Y}

/-- A bisimulation trivially gives a complete simulation. -/
theorem sb_css (h : sb L RR t t') : css L RR t t' :=
  ⟨h.1, fun l u hu => let ⟨l', t'', h', _⟩ := h.2 l u hu; ⟨l', t'', h'⟩⟩

theorem sbisim_clos_css {R : Rel (CTree E C X) (CTree F D Y)} (hR : Chain (css L) R) :
    ∀ (t t' : CTree E C X) (u' u : CTree F D Y), t ~ t' → R t' u' → u' ~ u → R t u := by
  refine tower (P := fun R : Rel (CTree E C X) (CTree F D Y) =>
    ∀ t t' u' u, t ~ t' → R t' u' → u' ~ u → R t u) ?_ ?_ R hR
  · intro T hT t t' u' u h₁ h₂ h₃
    exact Rel.inf_apply.2 fun R hR => hT R hR t t' u' u h₁ (Rel.inf_apply.1 h₂ R hR) h₃
  · intro R _ ih t t' u' u h₁ h₂ h₃
    refine ⟨fun l t₁ ht₁ => ?_, fun l u₁ hu₁ => ?_⟩
    · obtain ⟨_, t₁', ht₁', hs₁, rfl⟩ := (sbisim_unfold.1 h₁).1 l t₁ ht₁
      obtain ⟨l', u₁', hu₁', hR', hl⟩ := h₂.1 l t₁' ht₁'
      obtain ⟨_, u₁, hu₁, hs₂, rfl⟩ := (sbisim_unfold.1 h₃).1 l' u₁' hu₁'
      exact ⟨l', u₁, hu₁, ih _ _ _ _ hs₁ hR' hs₂, hl⟩
    · obtain ⟨_, u₁', hu₁', -, -⟩ := (sbisim_unfold.1 h₃).2 l u₁ hu₁
      obtain ⟨l', t₁', ht₁'⟩ := h₂.2 _ _ hu₁'
      obtain ⟨l'', t₁, ht₁, -, -⟩ := (sbisim_unfold.1 h₁).2 l' t₁' ht₁'
      exact ⟨l'', t₁, ht₁⟩

/-- Rewriting `~` on both sides of `cssim L` (the Rocq `sbisim_*clos_cssim_*` instances). -/
theorem sbisim_clos_cssim {t₀ : CTree E C X} {u₀ : CTree F D Y} (h₁ : t ~ t₀)
    (h₂ : cssim L t₀ u₀) (h₃ : u₀ ~ t') : cssim L t t' :=
  sbisim_clos_css (gfp_chain _) t t₀ u₀ t' h₁ h₂ h₃

theorem css_sb (h₁ : css L RR t t') (h₂ : css (flip L) (flip RR) t' t) : sb L RR t t' :=
  ⟨h₁.1, h₂.1⟩

end CompleteStrongSimulations

end CTree
