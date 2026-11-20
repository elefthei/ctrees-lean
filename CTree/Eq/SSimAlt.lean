/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.Epsilon

/-!
# An alternative strong simulation

`ss' L` is a simulation functor whose challenge does not go through the inductive `trans`
relation: a productive left tree plays a `trans` step, while a `br`/`guard` node on the left is
answered by an `Epsilon` path on the right. Its greatest fixpoint `ssim'` coincides with `ssim`
(`ssim_ssim'`), and it supports the up-to principles `epsilon_ctx_r_sst'` and `ss_sst'`
(← `Eq/SSimAlt.v`). `CTree` is extensional, so the Rocq up-to-`equ` closures and `Proper`
instances are omitted.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E F C D : Effect.{u}} {X Y X' Y' : Type u}

/-- The body of `ss'`, with separate relations for strong steps (`R`) and `epsilon` steps
(`Reps`). -/
def ss'_gen (L : Label E → Label F → Prop) (R Reps : Rel (CTree E C X) (CTree F D Y))
    (t : CTree E C X) (u : CTree F D Y) : Prop :=
  (Productive t → ∀ l t', trans l t t' → ∃ l' u', trans l' u u' ∧ R t' u' ∧ L l l') ∧
  (∀ (c : C.I) (k : C.O c → CTree E C X), t = .br c k →
    ∀ x, ∃ u', Epsilon u u' ∧ Reps (k x) u') ∧
  (∀ t', t = .guard t' → ∃ u', Epsilon u u' ∧ Reps t' u')

theorem ss'_gen_mon {L : Label E → Label F → Prop}
    {R R' Reps Reps' : Rel (CTree E C X) (CTree F D Y)}
    (hR : R ≤ R') (hReps : Reps ≤ Reps') {t : CTree E C X} {u : CTree F D Y}
    (h : ss'_gen L R Reps t u) : ss'_gen L R' Reps' t u :=
  ⟨fun hp l t' ht =>
    let ⟨l', u', h₁, h₂, h₃⟩ := h.1 hp l t' ht
    ⟨l', u', h₁, hR _ _ h₂, h₃⟩,
   fun c k hk x =>
    let ⟨u', h₁, h₂⟩ := h.2.1 c k hk x
    ⟨u', h₁, hReps _ _ h₂⟩,
   fun t' ht =>
    let ⟨u', h₁, h₂⟩ := h.2.2 t' ht
    ⟨u', h₁, hReps _ _ h₂⟩⟩

/-- The alternative strong simulation functor. -/
def ss' (L : Label E → Label F → Prop) : Mon (Rel (CTree E C X) (CTree F D Y)) where
  body R t u := ss'_gen L R R t u
  mono h _ _ H := ss'_gen_mon h h H

/-- The alternative strong simulation. -/
def ssim' (L : Label E → Label F → Prop) : Rel (CTree E C X) (CTree F D Y) := gfp (ss' L)

section Heterogeneous
variable {L : Label E → Label F → Prop} {R Reps : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem ssim'_unfold : ssim' L t u ↔ ss'_gen L (ssim' L) (ssim' L) t u :=
  ⟨fun h => gfp_pfp (b := ss' L) t u h, fun h => b_chain (gfp_chain (ss' L)) t u h⟩

theorem ss'_gen_br {c : C.I} {k : C.O c → CTree E C X} (h : ss'_gen L R Reps (.br c k) u)
    (x : C.O c) : ∃ u', Epsilon u u' ∧ Reps (k x) u' :=
  h.2.1 c k rfl x

theorem ss'_gen_guard (h : ss'_gen L R Reps (.guard t) u) : ∃ u', Epsilon u u' ∧ Reps t u' :=
  h.2.2 t rfl

/-- Stuck trees are simulated by anything. -/
theorem ss'_stuck : ss'_gen L R Reps (.stuck : CTree E C X) u :=
  ⟨fun _ _ _ ht => (trans_stuck_inv ht).elim, fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem ssim'_stuck : ssim' L (.stuck : CTree E C X) u := ssim'_unfold.2 ss'_stuck

end Heterogeneous

section Homogeneous
variable {L : Label E → Label E → Prop} {R Reps : Rel (CTree E C X) (CTree E C X)}

theorem ss'_gen_refl (hR : ∀ t, R t t) (hReps : ∀ t, Reps t t) (hL : ∀ l, L l l)
    (t : CTree E C X) : ss'_gen L R Reps t t :=
  ⟨fun _ l t' ht => ⟨l, t', ht, hR t', hL l⟩,
   fun _ k h x => ⟨k x, by subst h; exact .br x (.refl _), hReps _⟩,
   fun t' h => ⟨t', by subst h; exact .guard (.refl _), hReps _⟩⟩

theorem ss'_chain_refl (hL : ∀ l, L l l) (hR : Chain (ss' L) R) : ∀ t, R t t :=
  refl_chain (b := ss' L) (fun _ _ ih t => ss'_gen_refl ih ih hL t) R hR

end Homogeneous

/-! ## Proof rules -/

section ProofRules
variable {L : Label E → Label F → Prop} {R Reps : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem step_ss'_stuck : ss'_gen L R Reps (.stuck : CTree E C X) (.stuck : CTree F D Y) :=
  ss'_stuck

theorem step_ss'_ret {x : X} {y : Y} (hst : R .stuck .stuck) (hL : L (.val x) (.val y)) :
    ss'_gen L R Reps (pure x) (pure y) :=
  ⟨fun _ l t' ht => by
    obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    exact ⟨_, _, trans_ret y, hst, hL⟩,
   fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem step_ss'_ret_l {x : X} {y : Y} {u' : CTree F D Y} (hst : R .stuck .stuck)
    (hL : L (.val x) (.val y)) (hu : trans (.val y) u u') : ss'_gen L R Reps (pure x) u := by
  cases trans_val_inv hu
  exact ⟨fun _ l t' ht => by
    obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    exact ⟨_, _, hu, hst, hL⟩,
   fun _ _ h => by simp at h, fun _ h => by simp at h⟩

/-- Visible events are deterministic for the LTS: the itree-style rule. -/
theorem step_ss'_vis {e : E.I} {f : F.I} {k : E.O e → CTree E C X} {k' : F.O f → CTree F D Y}
    (h : ∀ x, ∃ y, R (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    ss'_gen L R Reps (.vis e k) (.vis f k') :=
  ⟨fun _ l t' ht => by
    obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
    obtain ⟨y, h₁, h₂⟩ := h x
    exact ⟨_, _, trans_vis y k', h₁, h₂⟩,
   fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem step_ss'_vis_id {e : E.I} {f : F.I} (hO : F.O f = E.O e) {k : E.O e → CTree E C X}
    {k' : F.O f → CTree F D Y}
    (h : ∀ x, R (k x) (k' (cast hO.symm x)) ∧ L (.obs e x) (.obs f (cast hO.symm x))) :
    ss'_gen L R Reps (.vis e k) (.vis f k') :=
  step_ss'_vis fun x => ⟨_, h x⟩

theorem step_ss'_vis_l {e : E.I} {k : E.O e → CTree E C X}
    (h : ∀ x, ∃ l' u', trans l' u u' ∧ R (k x) u' ∧ L (.obs e x) l') :
    ss'_gen L R Reps (.vis e k) u :=
  ⟨fun _ l t' ht => by
    obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
    exact h x,
   fun _ _ h => by simp at h, fun _ h => by simp at h⟩

/-- Delayed `br` nodes allow a coinductive step. -/
theorem step_ss'_br_l {c : C.I} {k : C.O c → CTree E C X} (h : ∀ x, Reps (k x) u) :
    ss'_gen L R Reps (.br c k) u :=
  ⟨fun hp => absurd hp (productive_br _ _),
   fun _ _ hk x => by
    obtain ⟨rfl, hk⟩ := br_eq_br_iff'.1 hk
    cases hk
    exact ⟨u, .refl _, h x⟩,
   fun _ h => by simp at h⟩

theorem step_ss'_br_r {c : D.I} {k : D.O c → CTree F D Y} (x : D.O c)
    (h : ss'_gen L R Reps t (k x)) : ss'_gen L R Reps t (.br c k) :=
  ⟨fun hp l t' ht =>
    let ⟨l', u', h₁, h₂, h₃⟩ := h.1 hp l t' ht
    ⟨l', u', trans_br x h₁, h₂, h₃⟩,
   fun c k hk y =>
    let ⟨u', h₁, h₂⟩ := h.2.1 c k hk y
    ⟨u', .br x h₁, h₂⟩,
   fun t' ht =>
    let ⟨u', h₁, h₂⟩ := h.2.2 t' ht
    ⟨u', .br x h₁, h₂⟩⟩

theorem step_ss'_br {a : C.I} {b : D.I} {k : C.O a → CTree E C X} {k' : D.O b → CTree F D Y}
    (h : ∀ x, ∃ y, Reps (k x) (k' y)) : ss'_gen L R Reps (.br a k) (.br b k') :=
  ⟨fun hp => absurd hp (productive_br _ _),
   fun _ _ hk x => by
    obtain ⟨rfl, hk⟩ := br_eq_br_iff'.1 hk
    cases hk
    obtain ⟨y, hy⟩ := h x
    exact ⟨k' y, .br y (.refl _), hy⟩,
   fun _ h => by simp at h⟩

theorem step_ss'_br_id {a : C.I} {b : D.I} (hO : D.O b = C.O a) {k : C.O a → CTree E C X}
    {k' : D.O b → CTree F D Y} (h : ∀ x, Reps (k x) (k' (cast hO.symm x))) :
    ss'_gen L R Reps (.br a k) (.br b k') :=
  step_ss'_br fun x => ⟨_, h x⟩

theorem step_ss'_guard_l (h : Reps t u) : ss'_gen L R Reps (.guard t) u :=
  ⟨fun hp => absurd hp (productive_guard _), fun _ _ h => by simp at h,
   fun _ ht => by cases guard_eq_guard_iff.1 ht; exact ⟨u, .refl _, h⟩⟩

theorem step_ss'_guard_r (h : ss'_gen L R Reps t u) : ss'_gen L R Reps t (.guard u) :=
  ⟨fun hp l t' ht =>
    let ⟨l', u', h₁, h₂, h₃⟩ := h.1 hp l t' ht
    ⟨l', u', trans_guard h₁, h₂, h₃⟩,
   fun c k hk y =>
    let ⟨u', h₁, h₂⟩ := h.2.1 c k hk y
    ⟨u', .guard h₁, h₂⟩,
   fun t' ht =>
    let ⟨u', h₁, h₂⟩ := h.2.2 t' ht
    ⟨u', .guard h₁, h₂⟩⟩

theorem step_ss'_guard {u : CTree F D Y} (h : Reps t u) :
    ss'_gen L R Reps (.guard t) (.guard u) :=
  ⟨fun hp => absurd hp (productive_guard _), fun _ _ h => by simp at h,
   fun _ ht => by cases guard_eq_guard_iff.1 ht; exact ⟨u, .guard (.refl _), h⟩⟩

theorem step_ss'_epsilon_r {u' : CTree F D Y} (h : ss'_gen L R Reps t u') (he : Epsilon u u') :
    ss'_gen L R Reps t u := by
  induction he with
  | refl => exact h
  | br x _ ih => exact step_ss'_br_r x (ih h)
  | guard _ ih => exact step_ss'_guard_r (ih h)

theorem ss'_gen_epsilon_l {t' : CTree E C X} (hReps : ∀ a b, Reps a b → ss'_gen L R Reps a b)
    (h : ss'_gen L R Reps t u) (he : Epsilon t t') : ss'_gen L R Reps t' u := by
  induction he generalizing u with
  | refl => exact h
  | br x _ ih =>
    obtain ⟨u', h₁, h₂⟩ := ss'_gen_br h x
    exact ih (step_ss'_epsilon_r (hReps _ _ h₂) h₁)
  | guard _ ih =>
    obtain ⟨u', h₁, h₂⟩ := ss'_gen_guard h
    exact ih (step_ss'_epsilon_r (hReps _ _ h₂) h₁)

/-- Visible `τ` nodes allow a coinductive step. -/
theorem step_ss'_step {u : CTree F D Y} (hL : L .tau .tau) (h : R t u) :
    ss'_gen L R Reps (.step t) (.step u) :=
  ⟨fun _ l t' ht => by
    obtain ⟨rfl, rfl⟩ := trans_step_inv ht
    exact ⟨_, _, trans_step u, h, hL⟩,
   fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem step_ss'_step_l (h : ∃ l' u', trans l' u u' ∧ R t u' ∧ L .tau l') :
    ss'_gen L R Reps (.step t) u :=
  ⟨fun _ l t' ht => by
    obtain ⟨rfl, rfl⟩ := trans_step_inv ht
    exact h,
   fun _ _ h => by simp at h, fun _ h => by simp at h⟩

end ProofRules

/-! ## Specialized proof rules -/

section SpecializedRules
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem ssim'_stuck' : ssim' L (.stuck : CTree E C X) (.stuck : CTree F D Y) := ssim'_stuck

theorem step_ssbt'_ret (hR : Chain (ss' L) R) {x : X} {y : Y} (hL : L (.val x) (.val y)) :
    ss' L R (pure x) (pure y) :=
  step_ss'_ret (b_chain hR _ _ ss'_stuck) hL

theorem ssim'_ret {x : X} {y : Y} (hL : L (.val x) (.val y)) :
    ssim' L (pure x : CTree E C X) (pure y : CTree F D Y) :=
  ssim'_unfold.2 (step_ssbt'_ret (gfp_chain _) hL)

theorem ssim'_step (hL : L .tau .tau) (h : ssim' L t u) : ssim' L (.step t) (.step u) :=
  ssim'_unfold.2 (step_ss'_step hL h)

theorem ssim'_guard (h : ssim' L t u) : ssim' L (.guard t) (.guard u) :=
  ssim'_unfold.2 (step_ss'_guard h)

theorem ssim'_br {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (h : ∀ x, ∃ y, ssim' L (k x) (k' y)) : ssim' L (.br c k) (.br d k') :=
  ssim'_unfold.2 (step_ss'_br h)

theorem ssim'_br_id {c : C.I} {d : D.I} (hO : D.O d = C.O c) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h : ∀ x, ssim' L (k x) (k' (cast hO.symm x))) :
    ssim' L (.br c k) (.br d k') :=
  ssim'_unfold.2 (step_ss'_br_id hO h)

theorem step_ssbt'_brS (hR : Chain (ss' L) R) {c : C.I} {d : D.I} {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (hL : L .tau .tau) (h : ∀ x, ∃ y, R (k x) (k' y)) :
    ss' L R (.brS c k) (.brS d k') :=
  step_ss'_br fun x =>
    let ⟨y, hy⟩ := h x
    ⟨y, b_chain hR _ _ (step_ss'_step hL hy)⟩

theorem ssim'_brS {c : C.I} {d : D.I} {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y}
    (hL : L .tau .tau) (h : ∀ x, ∃ y, ssim' L (k x) (k' y)) : ssim' L (.brS c k) (.brS d k') :=
  ssim'_unfold.2 (step_ssbt'_brS (gfp_chain _) hL h)

theorem step_ssbt'_brS_id (hR : Chain (ss' L) R) {c : C.I} {d : D.I} (hO : D.O d = C.O c)
    {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y} (hL : L .tau .tau)
    (h : ∀ x, R (k x) (k' (cast hO.symm x))) : ss' L R (.brS c k) (.brS d k') :=
  step_ssbt'_brS hR hL fun x => ⟨_, h x⟩

theorem ssim'_brS_id {c : C.I} {d : D.I} (hO : D.O d = C.O c) {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (hL : L .tau .tau) (h : ∀ x, ssim' L (k x) (k' (cast hO.symm x))) :
    ssim' L (.brS c k) (.brS d k') :=
  ssim'_unfold.2 (step_ssbt'_brS_id (gfp_chain _) hO hL h)

theorem ssim'_vis {e : E.I} {f : F.I} {k : E.O e → CTree E C X} {k' : F.O f → CTree F D Y}
    (h : ∀ x, ∃ y, ssim' L (k x) (k' y) ∧ L (.obs e x) (.obs f y)) :
    ssim' L (.vis e k) (.vis f k') :=
  ssim'_unfold.2 (step_ss'_vis h)

theorem ssim'_vis_id {e : E.I} {f : F.I} (hO : F.O f = E.O e) {k : E.O e → CTree E C X}
    {k' : F.O f → CTree F D Y}
    (h : ∀ x, ssim' L (k x) (k' (cast hO.symm x)) ∧ L (.obs e x) (.obs f (cast hO.symm x))) :
    ssim' L (.vis e k) (.vis f k') :=
  ssim'_unfold.2 (step_ss'_vis_id hO h)

theorem ssim'_vis_l {e : E.I} {k : E.O e → CTree E C X}
    (h : ∀ x, ∃ l' u', trans l' u u' ∧ ssim' L (k x) u' ∧ L (.obs e x) l') :
    ssim' L (.vis e k) u :=
  ssim'_unfold.2 (step_ss'_vis_l h)

theorem ssim'_epsilon_l {t' : CTree E C X} (h : ssim' L t u) (he : Epsilon t t') :
    ssim' L t' u :=
  ssim'_unfold.2 (ss'_gen_epsilon_l (fun _ _ h => ssim'_unfold.1 h) (ssim'_unfold.1 h) he)

end SpecializedRules

/-! ## Inversion rules -/

section InversionRules
variable {L : Label E → Label F → Prop} {R Reps : Rel (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem ss'_vis_l_inv {e : E.I} {k : E.O e → CTree E C X} (x : E.O e)
    (h : ss'_gen L R Reps (.vis e k) u) : ∃ l' u', trans l' u u' ∧ R (k x) u' ∧ L (.obs e x) l' :=
  h.1 (.vis e k) _ _ (trans_vis x k)

theorem ss'_step_l_inv (h : ss'_gen L R Reps (.step t) u) :
    ∃ l' u', trans l' u u' ∧ R t u' ∧ L .tau l' :=
  h.1 (.step t) _ _ (trans_step t)

end InversionRules

/-! ## Up-to principles -/

/-- `R` holds up to an `Epsilon` path. -/
def epsilon_ctx (R : Pred (CTree E C X)) (t : CTree E C X) : Prop := ∃ t', Epsilon t t' ∧ R t'

/-- `R` holds up to a `guard` prefix. -/
def epsilon_det_ctx (R : Pred (CTree E C X)) (t : CTree E C X) : Prop :=
  ∃ t', EpsilonDet t t' ∧ R t'

/-- Closure of the right-hand side under `Epsilon`. -/
def epsilon_ctx_r : Mon (Rel (CTree E C X) (CTree F D Y)) where
  body R t u := epsilon_ctx (fun u => R t u) u
  mono h t _ H := let ⟨u', h₁, h₂⟩ := H; ⟨u', h₁, h t u' h₂⟩

section Upto
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}

/-- Up-to `Epsilon` on the right. -/
theorem epsilon_ctx_r_sst' (hR : Chain (ss' L) R) : ∀ t u, epsilon_ctx_r R t u → R t u := by
  refine tower (P := fun R : Rel (CTree E C X) (CTree F D Y) =>
    ∀ t u, epsilon_ctx_r R t u → R t u) ?_ ?_ R hR
  · intro T hT t u ⟨u', he, h⟩
    exact Rel.inf_apply.2 fun R hR => hT R hR t u ⟨u', he, Rel.inf_apply.1 h R hR⟩
  · intro R _ _ t u ⟨u', he, h⟩
    exact step_ss'_epsilon_r h he

/-- Up-to `ss`: an `ss` step is always matched by one or more `ss'` steps. -/
theorem ss_sst' (hR : Chain (ss' L) R) : ∀ t u, ss L R t u → R t u := by
  refine tower (P := fun R : Rel (CTree E C X) (CTree F D Y) => ∀ t u, ss L R t u → R t u)
    ?_ ?_ R hR
  · intro T hT t u h
    exact Rel.inf_apply.2 fun R hR => hT R hR t u fun l t' ht =>
      let ⟨l', u', h₁, h₂, h₃⟩ := h l t' ht
      ⟨l', u', h₁, Rel.inf_apply.1 h₂ R hR, h₃⟩
  · intro R hR ih t u h
    have h' : ss L R t u := (ss L).mono (b_chain hR) t u h
    refine ⟨fun _ l t' ht => ?_, fun c k hk x => ?_, fun t' ht => ?_⟩
    · obtain ⟨l', u', h₁, h₂, h₃⟩ := h l t' ht
      exact ⟨l', u', h₁, b_chain hR _ _ h₂, h₃⟩
    · subst hk; exact ⟨u, .refl _, ih _ _ (ss_br_l_inv h' x)⟩
    · subst ht; exact ⟨u, .refl _, ih _ _ (ss_guard_l_inv h')⟩

end Upto

/-! ## Up-to `bind` -/

section Bind
variable {L : Label E → Label F → Prop} {R0 : X → Y → Prop}

/-- Chain elements of `ss' L` are closed under `bind`. -/
theorem ss'_chain_bind_gen {L0 : Label E → Label F → Prop} (hL0 : isUpdateValRel L R0 L0)
    {R : Rel (CTree E C X') (CTree F D Y')} (hR : Chain (ss' L) R) :
    ∀ (t : CTree E C X) (t' : CTree F D Y) (k : X → CTree E C X') (k' : Y → CTree F D Y'),
      ssim L0 t t' → (∀ x x', R0 x x' → R (k x) (k' x')) → R (t >>= k) (t' >>= k') := by
  refine tower (P := fun R : Rel (CTree E C X') (CTree F D Y') => ∀ t t' k k', ssim L0 t t' →
    (∀ x x', R0 x x' → R (k x) (k' x')) → R (t >>= k) (t' >>= k')) ?_ ?_ R hR
  · intro T hT t t' k k' htt' hkk'
    exact Rel.inf_apply.2 fun R hR =>
      hT R hR t t' k k' htt' fun x x' hx => Rel.inf_apply.1 (hkk' x x' hx) R hR
  · intro R hR ih t t' k k' htt' hkk'
    have ih' := fun t t' (h : ssim L0 t t') =>
      ih t t' k k' h fun x x' hx => b_chain hR _ _ (hkk' x x' hx)
    -- the right-hand answer to a value of `t`
    have val_r : ∀ x : X, trans (.val x) t .stuck →
        ∃ x', R0 x x' ∧ trans (.val x') t' .stuck := fun x hx => by
      obtain ⟨l', u', hu', -, hll'⟩ := ssim_unfold.1 htt' _ _ hx
      obtain ⟨v₂, rfl, hv⟩ := ((hL0 _ _ (wfVal_trans hx) (wfVal_trans hu')).2 hll').val_l
      cases trans_val_inv hu'
      exact ⟨v₂, hv, hu'⟩
    refine ⟨fun hp l u hu => ?_, fun c kk hk x => ?_, fun u hu => ?_⟩
    · rcases trans_bind_inv hu with ⟨hl, t₁, ht₁, rfl⟩ | ⟨x, hx, hk⟩
      · obtain ⟨l', t₁', ht₁', hss, hll'⟩ := ssim_unfold.1 htt' l t₁ ht₁
        obtain ⟨hl', hL⟩ :=
          ((hL0 l l' (wfVal_trans ht₁) (wfVal_trans ht₁')).2 hll').nonval_l hl
        exact ⟨l', t₁' >>= k', trans_bind_l hl' ht₁', ih' _ _ hss, hL⟩
      · obtain rfl := productive_epsilon (productive_bind hp) (trans_val_epsilon hx).1
        obtain ⟨x', hv, hu'⟩ := val_r x hx
        obtain ⟨l'', u'', hu'', hss', hll''⟩ :=
          (hkk' x x' hv).1 (by simpa using hp) l u hk
        exact ⟨l'', u'', trans_bind_r hu' hu'', hss', hll''⟩
    · rcases br_eq_bind_inv hk with ⟨v, rfl, hkv⟩ | ⟨k₀, rfl, hk₀⟩
      · obtain ⟨v', hv, hu'⟩ := val_r v (trans_ret v)
        obtain ⟨u', he, hr⟩ := (hkk' v v' hv).2.1 c kk hkv x
        exact ⟨u', epsilon_bind (trans_val_epsilon hu').1 he, hr⟩
      · exact ⟨t' >>= k', .refl _, hk₀ x ▸ ih' _ _ (ssim_br_l_inv htt' x)⟩
    · rcases guard_eq_bind_inv hu with ⟨v, rfl, hkv⟩ | ⟨t₀, rfl, hk₀⟩
      · obtain ⟨v', hv, hu'⟩ := val_r v (trans_ret v)
        obtain ⟨u', he, hr⟩ := (hkk' v v' hv).2.2 u hkv
        exact ⟨u', epsilon_bind (trans_val_epsilon hu').1 he, hr⟩
      · exact ⟨t' >>= k', .refl _, hk₀ ▸ ih' _ _ (ssim_guard_l_inv htt')⟩

theorem ss'_clo_bind_gen {L0 : Label E → Label F → Prop} (hL0 : isUpdateValRel L R0 L0)
    {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'} {k₂ : Y → CTree F D Y'}
    (h₁ : ssim L0 t₁ t₂) (h₂ : ∀ x y, R0 x y → ssim' L (k₁ x) (k₂ y)) :
    ssim' L (t₁ >>= k₁) (t₂ >>= k₂) :=
  ss'_chain_bind_gen hL0 (gfp_chain _) _ _ _ _ h₁ h₂

theorem ss'_clo_bind {R : Rel (CTree E C X') (CTree F D Y')} (hR : Chain (ss' L) R)
    {t : CTree E C X} {t' : CTree F D Y} {k : X → CTree E C X'} {k' : Y → CTree F D Y'}
    (h₁ : ssim (UpdateValRel L R0) t t') (h₂ : ∀ x x', R0 x x' → R (k x) (k' x')) :
    R (t >>= k) (t' >>= k') :=
  ss'_chain_bind_gen updateValRel_correct hR _ _ _ _ h₁ h₂

theorem ssim'_clo_bind {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'}
    {k₂ : Y → CTree F D Y'} (h₁ : ssim (UpdateValRel L R0) t₁ t₂)
    (h₂ : ∀ x y, R0 x y → ssim' L (k₁ x) (k₂ y)) : ssim' L (t₁ >>= k₁) (t₂ >>= k₂) :=
  ss'_clo_bind (gfp_chain _) h₁ h₂

end Bind

theorem ss'_clo_bind_eq {R : Rel (CTree E C X') (CTree E D X')} (hR : Chain (ss' Eq) R)
    {t : CTree E C X} {t' : CTree E D X} {k : X → CTree E C X'} {k' : X → CTree E D X'}
    (h₁ : t ≲ t') (h₂ : ∀ x, R (k x) (k' x)) : R (t >>= k) (t' >>= k') :=
  ss'_chain_bind_gen (R0 := Eq) updateValRel_eq hR _ _ _ _ h₁ (by rintro x _ rfl; exact h₂ x)

theorem ssim'_clo_bind_eq {t₁ : CTree E C X} {t₂ : CTree E D X} {k₁ : X → CTree E C X'}
    {k₂ : X → CTree E D X'} (h₁ : t₁ ≲ t₂) (h₂ : ∀ x, ssim' Eq (k₁ x) (k₂ x)) :
    ssim' Eq (t₁ >>= k₁) (t₂ >>= k₂) :=
  ss'_clo_bind_eq (gfp_chain _) h₁ h₂

/-! ## Equivalence with `ssim` -/

section Equiv
variable {L : Label E → Label F → Prop}

theorem ss_ss'_chain {R : Rel (CTree E C X) (CTree F D Y)} (hR : Chain (ss' L) R)
    {t : CTree E C X} {u : CTree F D Y} (h : ss L R t u) : ss' L R t u :=
  ⟨fun _ l t' ht => h l t' ht,
   fun _ _ hk x => by subst hk; exact ⟨u, .refl _, ss_sst' hR _ _ (ss_br_l_inv h x)⟩,
   fun _ ht => by subst ht; exact ⟨u, .refl _, ss_sst' hR _ _ (ss_guard_l_inv h)⟩⟩

/-- The alternative simulation `ssim'` is equivalent to `ssim`. -/
theorem ssim_ssim' {t : CTree E C X} {u : CTree F D Y} : ssim L t u ↔ ssim' L t u :=
  ⟨fun h => le_gfp (b := ss' L) (x := ssim L) (fun _ u h =>
      ⟨fun _ => ssim_unfold.1 h,
       fun _ _ hk x => by subst hk; exact ⟨u, .refl _, ssim_br_l_inv h x⟩,
       fun _ ht => by subst ht; exact ⟨u, .refl _, ssim_guard_l_inv h⟩⟩) t u h,
   fun h => le_gfp (b := ss L) (x := ssim' L) (fun _ _ h l t' ht => by
      obtain ⟨t₀, he, hp, ht₀⟩ := trans_epsilon ht
      exact (ssim'_unfold.1 (ssim'_epsilon_l h he)).1 hp l t' ht₀) t u h⟩

end Equiv

example (t : CTree E C X) : (CTree.spin : CTree E C X) ≲ t := by
  refine ssim_ssim'.2 ?_
  revert t
  coinduction R _ CIH
  intro u; rw [unfold_spin]; exact step_ss'_guard_l (CIH u)

end CTree
