/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.SBisim

/-!
# Internal paths

- `EpsilonDet t t'`: `t` is `t'` under a finite stack of `guard`s.
- `Productive t`: the head of `t` is observable (`ret`, `vis` or `step`).
- `Epsilon t t'`: `t'` is reachable from `t` through `br` and `guard` nodes.

(← `Eq/Epsilon.v`.) Structural equality is `=`, so the Rocq `Proper` instances are not needed.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E F C D : Effect.{u}} {X Y Z : Type u}

/-- `t` is `t'` under a finite stack of `guard`s. -/
inductive EpsilonDet : CTree E C X → CTree E C X → Prop
  | refl (t : CTree E C X) : EpsilonDet t t
  | guard {t t' : CTree E C X} : EpsilonDet t t' → EpsilonDet t.guard t'

/-- The head of the tree is observable. -/
inductive Productive : CTree E C X → Prop
  | ret (r : X) : Productive (pure r)
  | vis (e : E.I) (k : E.O e → CTree E C X) : Productive (.vis e k)
  | step (t : CTree E C X) : Productive (.step t)

/-- `t'` is reachable from `t` through `br` and `guard` nodes. -/
inductive Epsilon : CTree E C X → CTree E C X → Prop
  | refl (t : CTree E C X) : Epsilon t t
  | br {c : C.I} {k : C.O c → CTree E C X} (x : C.O c) {t : CTree E C X} :
      Epsilon (k x) t → Epsilon (.br c k) t
  | guard {u t : CTree E C X} : Epsilon u t → Epsilon u.guard t

/-! ## `EpsilonDet` -/

section EpsilonDet
variable {t t' t'' : CTree E C X}

theorem EpsilonDet.trans (h₁ : EpsilonDet t t') (h₂ : EpsilonDet t' t'') : EpsilonDet t t'' := by
  induction h₁ with
  | refl => exact h₂
  | guard _ ih => exact .guard (ih h₂)

theorem epsilon_det_bind {k : X → CTree E C Y} (h : EpsilonDet t t') :
    EpsilonDet (t >>= k) (t' >>= k) := by
  induction h with
  | refl => exact .refl _
  | guard _ ih => rw [guard_bind]; exact .guard ih

theorem epsilon_det_bind_ret_l {k : X → CTree E C Y} {u : CTree E C Y} {x : X}
    (h₁ : EpsilonDet t (pure x)) (h₂ : EpsilonDet (k x) u) : EpsilonDet (t >>= k) u := by
  generalize hx : (pure x : CTree E C X) = p at h₁
  induction h₁ with
  | refl => subst hx; rwa [pure_bind']
  | guard _ ih => rw [guard_bind]; exact .guard (ih hx)

theorem epsilon_det_bind_ret_l_equ {k : X → CTree E C Y} {x : X} (h : EpsilonDet t (pure x)) :
    t >>= k = t >>= fun _ => k x := by
  generalize hx : (pure x : CTree E C X) = p at h
  induction h with
  | refl => subst hx; simp
  | guard _ ih => simp only [guard_bind, guard_eq_guard_iff]; exact ih hx

theorem epsilon_det_trans {l : Label E} (h₁ : EpsilonDet t t') (h₂ : trans l t' t'') :
    trans l t t'' := by
  induction h₁ with
  | refl => exact h₂
  | guard _ ih => exact trans_guard (ih h₂)

theorem sbisim_epsilon_det (h : EpsilonDet t t') : t ~ t' := by
  induction h with
  | refl => exact sbisim_refl _
  | guard _ ih => exact sbisim_trans (sb_guard _) ih

end EpsilonDet

/-! ## `Productive` -/

section Productive

theorem ctree_case_productive (t : CTree E C X) :
    Productive t ∨ (∃ c k, t = .br c k) ∨ (∃ u, t = .guard u) ∨ t = .stuck := by
  cases t with
  | ret r => exact .inl (.ret r)
  | stuck => exact .inr (.inr (.inr rfl))
  | step t => exact .inl (.step t)
  | guard u => exact .inr (.inr (.inl ⟨u, rfl⟩))
  | vis e k => exact .inl (.vis e k)
  | br c k => exact .inr (.inl ⟨c, k, rfl⟩)

theorem productive_guard (t : CTree E C X) : ¬ Productive t.guard := by
  generalize ht : t.guard = s
  intro h; cases h <;> simp at ht

theorem productive_br (c : C.I) (k : C.O c → CTree E C X) : ¬ Productive (.br c k) := by
  generalize ht : CTree.br c k = s
  intro h; cases h <;> simp at ht

theorem productive_stuck : ¬ Productive (.stuck : CTree E C X) := by
  generalize ht : (CTree.stuck : CTree E C X) = s
  intro h; cases h <;> simp at ht

theorem productive_bind {t : CTree E C Y} {k : Y → CTree E C X} (h : Productive (t >>= k)) :
    Productive t := by
  cases t with
  | ret r => exact .ret r
  | stuck => rw [stuck_bind] at h; exact absurd h productive_stuck
  | step t => exact .step t
  | guard u => rw [guard_bind] at h; exact absurd h (productive_guard _)
  | vis e k => exact .vis e k
  | br c k => rw [br_bind] at h; exact absurd h (productive_br _ _)

end Productive

/-! ## `Epsilon` -/

section Epsilon
variable {t t' t'' u v : CTree E C X}

theorem epsilon_case (h : Epsilon t t') :
    t = t' ∨ (∃ c k x, t = .br c k ∧ Epsilon (k x) t') ∨ (∃ u, t = .guard u ∧ Epsilon u t') := by
  cases h with
  | refl => exact .inl rfl
  | br x h => exact .inr (.inl ⟨_, _, x, rfl, h⟩)
  | guard h => exact .inr (.inr ⟨_, rfl, h⟩)

theorem epsilon_trans {l : Label E} (h₁ : Epsilon t t') (h₂ : trans l t' t'') : trans l t t'' := by
  induction h₁ with
  | refl => exact h₂
  | br x _ ih => exact trans_br x (ih h₂)
  | guard _ ih => exact trans_guard (ih h₂)

theorem epsilon_fwd {c : C.I} {k : C.O c → CTree E C X} (x : C.O c) (h : Epsilon t (.br c k)) :
    Epsilon t (k x) := by
  generalize hb : CTree.br c k = b at h
  induction h with
  | refl => subst hb; exact .br x (.refl _)
  | br y _ ih => exact .br y (ih hb)
  | guard _ ih => exact .guard (ih hb)

theorem epsilon_fwd' (h : Epsilon t (.guard u)) : Epsilon t u := by
  generalize hg : u.guard = g at h
  induction h with
  | refl => subst hg; exact .guard (.refl _)
  | br y _ ih => exact .br y (ih hg)
  | guard _ ih => exact .guard (ih hg)

theorem trans_epsilon {l : Label E} (h : trans l t t'') :
    ∃ t', Epsilon t t' ∧ Productive t' ∧ trans l t' t'' := by
  unfold trans at h
  rw [← fold_unfold t]
  generalize t.unfold = T at h
  induction h with
  | br x _ ih =>
    obtain ⟨t', h₁, h₂, h₃⟩ := ih
    rw [fold_unfold] at h₁
    exact ⟨t', .br x h₁, h₂, h₃⟩
  | guard _ ih =>
    obtain ⟨t', h₁, h₂, h₃⟩ := ih
    rw [fold_unfold] at h₁
    exact ⟨t', .guard h₁, h₂, h₃⟩
  | step => exact ⟨_, .refl _, .step _, trans_step _⟩
  | obs x => exact ⟨_, .refl _, .vis _ _, trans_vis x _⟩
  | val => exact ⟨_, .refl _, .ret _, trans_ret _⟩

theorem trans_val_epsilon {x : X} (h : trans (.val x) t t') : Epsilon t (pure x) ∧ t' = .stuck := by
  obtain ⟨u, h₁, h₂, h₃⟩ := trans_epsilon h
  cases h₂ with
  | ret r =>
    obtain ⟨rfl, e⟩ := trans_ret_inv h₃
    cases val_eq_inv e
    exact ⟨h₁, rfl⟩
  | vis => obtain ⟨_, _, e⟩ := trans_vis_inv h₃; cases e
  | step => cases (trans_step_inv h₃).2

theorem trans_τ_epsilon (h : trans .tau t t') : ∃ u, Epsilon t (.step u) ∧ t' = u := by
  obtain ⟨u, h₁, h₂, h₃⟩ := trans_epsilon h
  cases h₂ with
  | ret => cases (trans_ret_inv h₃).2
  | vis => obtain ⟨_, _, e⟩ := trans_vis_inv h₃; cases e
  | step => exact ⟨_, h₁, (trans_step_inv h₃).1⟩

theorem trans_obs_epsilon {e : E.I} {x : E.O e} (h : trans (.obs e x) t t') :
    ∃ k, Epsilon t (.vis e k) ∧ t' = k x := by
  obtain ⟨u, h₁, h₂, h₃⟩ := trans_epsilon h
  cases h₂ with
  | ret => cases (trans_ret_inv h₃).2
  | vis e' k =>
    obtain ⟨y, rfl, el⟩ := trans_vis_inv h₃
    obtain ⟨rfl, hxy⟩ := obs_eq_inv el
    cases hxy
    exact ⟨k, h₁, rfl⟩
  | step => cases (trans_step_inv h₃).2

theorem productive_epsilon (hp : Productive t) (h : Epsilon t t') : t = t' := by
  cases h with
  | refl => rfl
  | br => exact absurd hp (productive_br _ _)
  | guard => exact absurd hp (productive_guard _)

theorem Epsilon.trans (h₁ : Epsilon t u) (h₂ : Epsilon u v) : Epsilon t v := by
  induction h₁ with
  | refl => exact h₂
  | br x _ ih => exact .br x (ih h₂)
  | guard _ ih => exact .guard (ih h₂)

theorem epsilon_bind_l {k : X → CTree E C Y} (h : Epsilon t t') : Epsilon (t >>= k) (t' >>= k) := by
  induction h with
  | refl => exact .refl _
  | br x _ ih => rw [br_bind]; exact .br x ih
  | guard _ ih => rw [guard_bind]; exact .guard ih

theorem epsilon_bind_ret {k : X → CTree E C Y} {x : X} (h : Epsilon t (pure x)) :
    Epsilon (t >>= k) (k x) := by
  simpa using epsilon_bind_l (k := k) h

theorem epsilon_bind {k : X → CTree E C Y} {w : CTree E C Y} {x : X} (h₁ : Epsilon t (pure x))
    (h₂ : Epsilon (k x) w) : Epsilon (t >>= k) w :=
  (epsilon_bind_ret h₁).trans h₂

theorem epsilon_bind_inv {k : X → CTree E C Y} {w : CTree E C Y} (h : Epsilon (t >>= k) w) :
    (∃ u', w = u' >>= k ∧ Epsilon t u') ∨ (∃ x, Epsilon t (pure x) ∧ Epsilon (k x) w) := by
  generalize hs : t >>= k = s at h
  induction h generalizing t with
  | refl => exact .inl ⟨t, hs.symm, .refl _⟩
  | br x h ih =>
    rcases br_eq_bind_inv hs with ⟨r, rfl, hk⟩ | ⟨k₀, rfl, hk⟩
    · exact .inr ⟨r, .refl _, hk ▸ .br x h⟩
    · rcases ih (hk x).symm with ⟨u', rfl, h'⟩ | ⟨r, h₁, h₂⟩
      · exact .inl ⟨u', rfl, .br x h'⟩
      · exact .inr ⟨r, .br x h₁, h₂⟩
  | guard h ih =>
    rcases guard_eq_bind_inv hs with ⟨r, rfl, hk⟩ | ⟨t₀, rfl, hk⟩
    · exact .inr ⟨r, .refl _, hk ▸ .guard h⟩
    · rcases ih hk with ⟨u', rfl, h'⟩ | ⟨r, h₁, h₂⟩
      · exact .inl ⟨u', rfl, .guard h'⟩
      · exact .inr ⟨r, .guard h₁, h₂⟩

theorem epsilon_det_epsilon (h : EpsilonDet t t') : Epsilon t t' := by
  induction h with
  | refl => exact .refl _
  | guard _ ih => exact .guard ih

end Epsilon

/-! ## Simulations up to `Epsilon` -/

section Sim
variable {L : Label E → Label F → Prop} {R : Rel (CTree E C X) (CTree F D Y)}
  {t t₀ : CTree E C X} {u u₀ : CTree F D Y}

theorem ss_epsilon_l (h₁ : Epsilon t₀ t) (h₂ : ss L R t₀ u) : ss L R t u :=
  fun _ _ ht => h₂ _ _ (epsilon_trans h₁ ht)

theorem ss_epsilon_l' (h : ∀ t₀, Epsilon t t₀ → Productive t₀ → ss L R t₀ u) : ss L R t u :=
  fun _ _ ht =>
    let ⟨t₀, h₁, h₂, h₃⟩ := trans_epsilon ht
    h t₀ h₁ h₂ _ _ h₃

theorem ss_epsilon_r (h₁ : Epsilon u u₀) (h₂ : ss L R t u₀) : ss L R t u :=
  fun l t' ht =>
    let ⟨l', u', h₃, h₄, h₅⟩ := h₂ l t' ht
    ⟨l', u', epsilon_trans h₁ h₃, h₄, h₅⟩

theorem ssim_epsilon_l (h₁ : Epsilon t₀ t) (h₂ : ssim L t₀ u) : ssim L t u :=
  ssim_unfold.2 (ss_epsilon_l h₁ (ssim_unfold.1 h₂))

theorem ssim_epsilon_l' (h : ∀ t₀, Epsilon t t₀ → Productive t₀ → ssim L t₀ u) : ssim L t u :=
  ssim_unfold.2 (ss_epsilon_l' fun t₀ h₁ h₂ => ssim_unfold.1 (h t₀ h₁ h₂))

theorem ssim_epsilon_r (h₁ : Epsilon u u₀) (h₂ : ssim L t u₀) : ssim L t u :=
  ssim_unfold.2 (ss_epsilon_r h₁ (ssim_unfold.1 h₂))

theorem ssim_ret_epsilon [RespectsVal L] {r : X} (h : ssim L (pure r : CTree E C X) u) :
    ∃ r' : Y, Epsilon u (pure r') ∧ L (.val r) (.val r') := by
  obtain ⟨l', u', hu, -, hl⟩ := ssim_unfold.1 h _ _ (trans_ret r)
  obtain ⟨y⟩ := (RespectsVal.respects_val _ _ hl).1 (.val r)
  cases trans_val_invT hu
  exact ⟨y, (trans_val_epsilon hu).1, hl⟩

theorem ssim_vis_epsilon [RespectsVal L] [RespectsTau L] {e : E.I} {k : E.O e → CTree E C X}
    (h : ssim L (.vis e k) u) (x : E.O e) :
    ∃ (e' : F.I) (k' : F.O e' → CTree F D Y) (y : F.O e'),
      Epsilon u (.vis e' k') ∧ ssim L (k x) (k' y) ∧ L (.obs e x) (.obs e' y) := by
  obtain ⟨l', u'', hu, hs, hl⟩ := ssim_unfold.1 h _ _ (trans_vis x k)
  obtain ⟨u', h₁, h₂, h₃⟩ := trans_epsilon hu
  cases h₂ with
  | ret =>
    obtain ⟨-, rfl⟩ := trans_ret_inv h₃
    exact absurd ((RespectsVal.respects_val _ _ hl).2 (.val _)) isVal_obs
  | vis e' k' =>
    obtain ⟨y, rfl, rfl⟩ := trans_vis_inv h₃
    exact ⟨e', k', y, h₁, hs, hl⟩
  | step =>
    obtain ⟨-, rfl⟩ := trans_step_inv h₃
    cases (RespectsTau.respects_tau _ _ hl).2 rfl

theorem ssim_brS_epsilon [RespectsTau L] {c : C.I} {k : C.O c → CTree E C X}
    (h : ssim L (.brS c k) u) (x : C.O c) : ∃ v, Epsilon u (.step v) ∧ ssim L (k x) v := by
  obtain ⟨l', u'', hu, hs, hl⟩ := ssim_unfold.1 h _ _ (trans_brS k x)
  cases (RespectsTau.respects_tau _ _ hl).1 rfl
  obtain ⟨v, h₁, rfl⟩ := trans_τ_epsilon hu
  exact ⟨_, h₁, hs⟩

end Sim

end CTree
