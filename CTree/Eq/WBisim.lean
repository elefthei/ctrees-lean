/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.SBisim

/-!
# Weak bisimulation

`ws` is the weak simulation functor: `trans` plays are answered by `wtrans`. `wb` is its
symmetrisation and `wbisim` its greatest fixpoint, written `t ≈ u` (← `Eq/WBisim.v`). `es` is the
one-sided expansion functor (answers by `etrans`). Weak bisimilarity is an equivalence relation
containing `sbisim`, but up-to transitivity is not valid (`not_Transitive_wt`). `CTree` is
extensional, so the Rocq up-to-`equ` closures and `Proper` instances are omitted.

Rocq `step` on a goal `wbisim t u` is `wbisim_unfold.2`; on a hypothesis it is `wbisim_unfold.1`.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E C : Effect.{u}} {X X' : Type u}

/-- The weak simulation functor. -/
def ws : Mon (Rel (CTree E C X) (CTree E C X)) where
  body R p q := ∀ l p', trans l p p' → ∃ q', wtrans l q q' ∧ R p' q'
  mono h _ _ H l p' hp := let ⟨q', h₁, h₂⟩ := H l p' hp; ⟨q', h₁, h _ _ h₂⟩

/-- The weak bisimulation functor: `ws` intersected with its symmetrised version. -/
def wb : Mon (Rel (CTree E C X) (CTree E C X)) where
  body R p q := ws R p q ∧ ws (converse _ R) q p
  mono h p q H := ⟨ws.mono h p q H.1, ws.mono (fun a b => h b a) q p H.2⟩

/-- The one-sided expansion functor. -/
def es : Mon (Rel (CTree E C X) (CTree E C X)) where
  body R p q := ∀ l p', trans l p p' → ∃ q', etrans l q q' ∧ R p' q'
  mono h _ _ H l p' hp := let ⟨q', h₁, h₂⟩ := H l p' hp; ⟨q', h₁, h _ _ h₂⟩

/-- Weak bisimilarity. -/
def wbisim : Rel (CTree E C X) (CTree E C X) := gfp wb

scoped instance : HasEquiv (CTree E C X) := ⟨wbisim⟩

variable {R : Rel (CTree E C X) (CTree E C X)} {t u v : CTree E C X}

theorem wbisim_unfold : t ≈ u ↔ wb wbisim t u :=
  ⟨fun h => gfp_pfp (b := wb) t u h, fun h => b_chain (gfp_chain wb) t u h⟩

/-! ## Elementary properties -/

theorem s_e (h : ss Eq R t u) : es R t u := fun l t' ht =>
  let ⟨_, u', hu, h', hl⟩ := h l t' ht; ⟨u', hl ▸ trans_etrans hu, h'⟩

theorem e_w (h : es R t u) : ws R t u := fun l t' ht =>
  let ⟨u', hu, h'⟩ := h l t' ht; ⟨u', etrans_wtrans hu, h'⟩

theorem s_w (h : ss Eq R t u) : ws R t u := e_w (s_e h)

/-- `wb` is the symmetrisation of `ws`. -/
theorem wb_symmetrical : Symmetrical (converse _) (wb : Mon (Rel (CTree E C X) _)) ws where
  invol _ := rfl
  eq S := funext fun t => funext fun u => propext <| by
    show wb S t u ↔ cap (ws S) (converse _ (ws (converse _ S))) t u
    rw [Rel.cap_apply]; rfl

theorem sbisim_wbisim (h : t ~ u) : t ≈ u :=
  le_gfp (b := wb) (x := sbisim Eq) (fun _ _ h =>
    let h := sbisim_unfold.1 h
    ⟨s_w h.1, s_w (ss_flip (fun _ _ h => h.symm) h.2)⟩) t u h

/-- Chain elements of `wb` contain `wbisim`, hence are reflexive (Rocq `refl_t`). -/
theorem refl_t (hR : Chain wb R) (t : CTree E C X) : R t t :=
  gfp_le_chain hR t t (sbisim_wbisim (sbisim_refl t))

/-- Chain elements of `wb` are symmetric (Rocq `sym_t`). -/
theorem sym_t (hR : Chain wb R) : ∀ t u, R t u → R u t := symm_symchain wb_symmetrical R hR

/-- Rocq `cnv_wt`, `cnv_gfp`, `cnv_wbisim`. -/
theorem cnv_wt (hR : Chain wb R) : R t u ↔ R u t := ⟨sym_t hR t u, sym_t hR u t⟩

theorem wbisim_symm (h : t ≈ u) : u ≈ t := sym_t (gfp_chain wb) t u h

/-! ## Transitivity -/

/-- Rocq `wbisim_trans_back` (and its duplicate `wbisim_trans_back'`). -/
theorem wbisim_trans_back {l : Label E} {u' : CTree E C X} (h : t ≈ u) (hu : trans l u u') :
    ∃ t', wtrans l t t' ∧ t' ≈ u' :=
  (wbisim_unfold.1 h).2 l u' hu

theorem wbisim_etrans_back {l : Label E} {u' : CTree E C X} (h : t ≈ u) (hu : etrans l u u') :
    ∃ t', wtrans l t t' ∧ t' ≈ u' := by
  rcases etrans_case hu with hu | ⟨rfl, rfl⟩
  · exact wbisim_trans_back h hu
  · exact ⟨t, wnil, h⟩

theorem wbisim_τs_back {u' : CTree E C X} (h : t ≈ u) (hu : Star (trans .tau) u u') :
    ∃ t', Star (trans .tau) t t' ∧ t' ≈ u' := by
  induction hu with
  | refl => exact ⟨t, .refl, h⟩
  | tail _ hs ih =>
    obtain ⟨t₁, h₁, h₂⟩ := ih
    obtain ⟨t', h₃, h₄⟩ := wbisim_trans_back h₂ hs
    exact ⟨t', h₁.trans (wtrans_τ.1 h₃), h₄⟩

theorem wbisim_wtrans_back {l : Label E} {u' : CTree E C X} (h : t ≈ u) (hu : wtrans l u u') :
    ∃ t', wtrans l t t' ∧ t' ≈ u' := by
  obtain ⟨u₁, u₂, h₁, h₂, h₃⟩ := hu
  obtain ⟨t₁, g₁, e₁⟩ := wbisim_τs_back h h₁
  obtain ⟨t₂, g₂, e₂⟩ := wbisim_etrans_back e₁ h₂
  obtain ⟨t', g₃, e₃⟩ := wbisim_τs_back e₂ h₃
  exact ⟨t', wconss (wtrans_τ.2 g₁) (wsnocs g₂ (wtrans_τ.2 g₃)), e₃⟩

theorem wbisim_trans_front {l : Label E} {t' : CTree E C X} (ht : trans l t t') (h : t ≈ u) :
    ∃ u', t' ≈ u' ∧ wtrans l u u' :=
  let ⟨u', h₁, h₂⟩ := wbisim_trans_back (wbisim_symm h) ht; ⟨u', wbisim_symm h₂, h₁⟩

theorem wbisim_etrans_front {l : Label E} {t' : CTree E C X} (ht : etrans l t t') (h : t ≈ u) :
    ∃ u', t' ≈ u' ∧ wtrans l u u' :=
  let ⟨u', h₁, h₂⟩ := wbisim_etrans_back (wbisim_symm h) ht; ⟨u', wbisim_symm h₂, h₁⟩

/-- Rocq `wbisim_wtrans_front` and `wbisim_wtrans_front_`. -/
theorem wbisim_wtrans_front {l : Label E} {t' : CTree E C X} (ht : wtrans l t t') (h : t ≈ u) :
    ∃ u', t' ≈ u' ∧ wtrans l u u' :=
  let ⟨u', h₁, h₂⟩ := wbisim_wtrans_back (wbisim_symm h) ht; ⟨u', wbisim_symm h₂, h₁⟩

/-- Weak bisimilarity is transitive (Rocq `Transitive_wbisim`), although up-to transitivity is not
valid. -/
theorem wbisim_trans (h₁ : t ≈ u) (h₂ : u ≈ v) : t ≈ v := by
  let S : Rel (CTree E C X) (CTree E C X) := fun x z => ∃ y, x ≈ y ∧ y ≈ z
  refine le_gfp (b := wb) (x := S) (wb_symmetrical.pfp ?_ ?_) t v ⟨u, h₁, h₂⟩
  · rintro x z ⟨y, h₁, h₂⟩; exact ⟨y, wbisim_symm h₂, wbisim_symm h₁⟩
  · rintro x z ⟨y, h₁, h₂⟩ l x' hx
    obtain ⟨y', hy, h₃⟩ := (wbisim_unfold.1 h₁).1 l x' hx
    obtain ⟨z', h₄, hz⟩ := wbisim_wtrans_front hy h₂
    exact ⟨z', hz, y', h₃, h₄⟩

theorem wbisim_equivalence : Equivalence (wbisim : Rel (CTree E C X) _) :=
  ⟨fun t => refl_t (gfp_chain wb) t, wbisim_symm, wbisim_trans⟩

/-- `wbisim` is closed under `sbisim` (Rocq `sbisim_wbisim_closed_goal`/`_ctx`). -/
theorem sbisim_wbisim_closed {t' u' : CTree E C X} (h₁ : t ~ t') (h₂ : t' ≈ u') (h₃ : u' ~ u) :
    t ≈ u :=
  wbisim_trans (sbisim_wbisim h₁) (wbisim_trans h₂ (sbisim_wbisim h₃))

/-! ## Both kinds of `tau` are ignored -/

theorem guard_wb (t : CTree E C X) : CTree.guard t ≈ t := sbisim_wbisim (sb_guard t)

theorem step_wb (t : CTree E C X) : CTree.step t ≈ t :=
  wbisim_unfold.2 ⟨fun l t' h => by
    obtain ⟨rfl, rfl⟩ := trans_step_inv h
    exact ⟨t', wnil, refl_t (gfp_chain wb) t'⟩,
   fun l t' h => ⟨t', wtrans_step (trans_wtrans h), refl_t (gfp_chain wb) t'⟩⟩

/-- Arbitrary chain elements of `wb` are not transitive. -/
theorem not_Transitive_wt (x : X) (e : E.I) (z : E.O e) :
    ¬ ∀ R, Chain (wb : Mon (Rel (CTree E C X) _)) R → ∀ t u v, R t u → R u v → R t v := by
  intro H
  have key : (CTree.vis e fun _ => pure x : CTree E C X) ≈ pure x := by
    coinduction R hR CIH
    have hT := H _ (.step hR)
    have hg : ∀ t u, t ≈ u → wb R t u := gfp_le_chain (.step hR)
    have main : wb R (.step (.vis e fun _ => pure x)) (.step (pure x)) :=
      ⟨fun l t' h => by
        obtain ⟨rfl, rfl⟩ := trans_step_inv h
        exact ⟨pure x, trans_wtrans (trans_step _), CIH⟩,
       fun l t' h => by
        obtain ⟨rfl, rfl⟩ := trans_step_inv h
        exact ⟨_, trans_wtrans (trans_step _), CIH⟩⟩
    exact hT _ _ _ (hg _ _ (wbisim_symm (step_wb _))) (hT _ _ _ main (hg _ _ (step_wb _)))
  obtain ⟨u', hu, -⟩ := (wbisim_unfold.1 key).1 (.obs e z) _ (trans_vis z _)
  rcases wtrans_ret_inv hu with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

/-- Rocq `step_wb_brS`; the shared branch type becomes `hO : C.O d = C.O c`. -/
theorem step_wb_brS (_hR : Chain wb R) {c d : C.I} (hO : C.O d = C.O c)
    {k : C.O c → CTree E C X} {k' : C.O d → CTree E C X} (h : ∀ x, R (k x) (k' (cast hO.symm x))) :
    wb R (.brS c k) (.brS d k') :=
  ⟨fun l t' ht => by
    obtain ⟨x, rfl, rfl⟩ := trans_brS_inv ht
    exact ⟨_, trans_wtrans (trans_brS _ _), h x⟩,
   fun l u' hu => by
    obtain ⟨y, rfl, rfl⟩ := trans_brS_inv hu
    refine ⟨_, trans_wtrans (trans_brS _ (cast hO y)), ?_⟩
    have := h (cast hO y)
    rwa [cast_cast, cast_eq] at this⟩

/-! ## Up-to `bind` -/

private theorem bind_chain_ws {R : Rel (CTree E C X') (CTree E C X')}
    (ih : ∀ (t u : CTree E C X) (k k' : X → CTree E C X'), t ≈ u →
      (∀ x, R (k x) (k' x)) → R (t >>= fun x => .step (k x)) (u >>= fun x => .step (k' x)))
    {t u : CTree E C X} {k k' : X → CTree E C X'} (htu : t ≈ u) (hk : ∀ x, R (k x) (k' x)) :
    ws R (t >>= fun x => .step (k x)) (u >>= fun x => .step (k' x)) := by
  intro l p' hp
  rcases trans_bind_inv hp with ⟨hl, t', ht, rfl⟩ | ⟨x, hx, hs⟩
  · obtain ⟨u', hu, h'⟩ := (wbisim_unfold.1 htu).1 l t' ht
    exact ⟨_, wtrans_bind_l hl hu, ih _ _ _ _ h' hk⟩
  · obtain ⟨rfl, rfl⟩ := trans_step_inv hs
    obtain ⟨u', hu, -⟩ := (wbisim_unfold.1 htu).1 _ _ hx
    obtain ⟨_, _, _, rfl⟩ := wtrans_val_inv' hu
    exact ⟨_, wtrans_bind_r' hu ⟨_, _, .refl, trans_step _, .refl⟩, hk x⟩

/-- Up-to `bind` for weak bisimulation, valid only when the continuation is guarded by a `step`. -/
theorem wb_chain_bind_gen {R : Rel (CTree E C X') (CTree E C X')} (hR : Chain wb R) :
    ∀ (t u : CTree E C X) (k k' : X → CTree E C X'), t ≈ u → (∀ x, R (k x) (k' x)) →
      R (t >>= fun x => .step (k x)) (u >>= fun x => .step (k' x)) := by
  refine tower (P := fun R : Rel (CTree E C X') (CTree E C X') =>
    ∀ (t u : CTree E C X) (k k' : X → CTree E C X'), t ≈ u → (∀ x, R (k x) (k' x)) →
      R (t >>= fun x => .step (k x)) (u >>= fun x => .step (k' x))) ?_ ?_ R hR
  · intro T hT t u k k' h₁ h₂
    exact Rel.inf_apply.2 fun R hR => hT R hR t u k k' h₁ fun x => Rel.inf_apply.1 (h₂ x) R hR
  · intro R hR ih t u k k' htu hk
    have hk' : ∀ x, R (k x) (k' x) := fun x => b_chain hR _ _ (hk x)
    refine ⟨bind_chain_ws ih htu hk', ws.mono (fun a b h => sym_t hR a b h) _ _ ?_⟩
    exact bind_chain_ws (fun _ _ _ _ h₁ h₂ => sym_t hR _ _
      (ih _ _ _ _ (wbisim_symm h₁) fun x => sym_t hR _ _ (h₂ x))) (wbisim_symm htu)
      fun x => sym_t hR _ _ (hk' x)

/-- Rocq `wbisim_ret_inv` (the unused `B0 -< C` hypothesis is dropped). -/
theorem wbisim_ret_inv {x y : X} (h : (pure x : CTree E C X) ≈ pure y) : x = y := by
  obtain ⟨u', hu, -⟩ := (wbisim_unfold.1 h).1 _ _ (trans_ret x)
  rcases wtrans_ret_inv hu with ⟨h, -⟩ | ⟨h, -⟩
  · cases h
  · exact val_eq_inv h

end CTree
