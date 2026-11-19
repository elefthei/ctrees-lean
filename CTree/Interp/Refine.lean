/- SPDX-License-Identifier: MIT -/
module

public import CTree.Interp.FoldStateT
public import CTree.Eq.SSimAlt
public import CTree.Misc.Pure

/-!
# Refinement of branches

Implementing the branches of a tree by finite pure trees yields a tree simulated by the original
one: `refine_ctree_ssim` for the `CTree` monad and `refine_state_ssim` for the state monad over it
(← `Interp/Refine.v`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)
open Coinduction

variable {E F B C : Effect.{u}} {X : Type u}

/-- A finite pure tree is simulated by a return, as long as its values are related to it. -/
theorem ssim_pure (L : Label E → Label F → Prop) (t : CTree E B X) (h : PureFinite t)
    (hL : ∀ x : X, L (.val x) (.val (⟨⟩ : PUnit))) :
    ssim L t (pure ⟨⟩ : CTree F C PUnit) := by
  induction h with
  | ret v => exact ssim_ret _ _ (hL v)
  | stuck => exact stuck_ssim
  | br _ _ _ ih => exact ssim_br_l ih
  | guard _ _ ih => exact ssim_guard_l ih

/-- Implementing the branches of a tree by finite pure trees refines it. -/
theorem refine_ctree_ssim {B' : Effect.{u}} (t : CTree E B X) (h : (c : B.I) → CTree E B' (B.O c))
    (hh : ∀ c, PureFinite (h c)) : refine h t ≲ t := by
  rw [ssim_ssim']
  refine coinduction (b := ss' Eq) (fun t : CTree E B X => refine h t) id ?_ t
  intro R hR CIH t
  show ss'_gen Eq R R _ _
  cases t with
  | ret x => rw [refine_ret]; exact step_ssbt'_ret hR rfl
  | stuck => rw [unfold_refine]; simpa using step_ss'_stuck
  | step t => simpa using step_ss'_step rfl (b_chain hR _ _ (step_ss'_guard_l (CIH t)))
  | guard t => simpa using step_ss'_guard (CIH t)
  | vis e k =>
    simp only [refine_vis, mtrigger, CTree.trigger', CTree.vis', vis_bind, pure_bind', id]
    exact step_ss'_vis fun x => ⟨x, b_chain hR _ _ (step_ss'_guard_l (CIH (k x))), rfl⟩
  | br c k =>
    rw [refine_br, ← pure_bind' (PUnit.unit : PUnit) fun _ => CTree.br c k]
    exact ss'_clo_bind (R0 := fun _ _ => True) (.step hR)
      (ssim_pure _ _ (hh c) fun x => .val x PUnit.unit trivial)
      fun x _ _ => step_ss'_br_r x (step_ss'_guard_l (CIH (k x)))

/-- The relation between the results of a stateful computation and of the original one. -/
def Rrr {St : Type u} (p : X × St) (x : X) : Prop := p.1 = x

/-- Labels of a stateful computation and of the original one. -/
abbrev Lrr (St : Type u) (E : Effect.{u}) (X : Type u) : Label E → Label E → Prop :=
  liftValRel (@Rrr X St)

/-- Implementing the branches of a tree by finite pure stateful computations refines it, up to
dropping the final state. -/
theorem refine_state_ssim {B' : Effect.{u}} {St : Type u} (t : CTree E B X)
    (h : (c : B.I) → StateT St (CTree E B') (B.O c)) (hh : ∀ c s, PureFinite (h c s)) (s : St) :
    ssim (Lrr St E X) (refine_state h t s) t := by
  rw [ssim_ssim']
  refine coinduction (b := ss' (Lrr St E X)) (fun p : CTree E B X × St => refine_state h p.1 p.2)
    (fun p => p.1) ?_ (t, s)
  rintro R hR CIH ⟨t, s⟩
  show ss'_gen _ R R _ _
  have hτ : Lrr St E X .tau .tau := .nonval _ _ isVal_tau isVal_tau rfl
  cases t with
  | ret x => rw [refine_state_ret]; exact step_ssbt'_ret hR (.val _ _ rfl)
  | stuck => rw [refine_state_stuck]; exact step_ss'_stuck
  | step t =>
    rw [refine_state_step]
    exact step_ss'_step hτ (b_chain hR _ _ (step_ss'_guard_l (CIH (t, s))))
  | guard t => rw [refine_state_guard]; exact step_ss'_guard (CIH (t, s))
  | vis e k =>
    simp only [refine_state_vis, mtrigger, CTree.trigger', CTree.vis', vis_bind, pure_bind']
    exact step_ss'_vis fun x => ⟨x, b_chain hR _ _ (step_ss'_guard_l (CIH (k x, s))),
      .nonval _ _ isVal_obs isVal_obs rfl⟩
  | br c k =>
    rw [refine_state_br, ← pure_bind' (PUnit.unit : PUnit) fun _ => CTree.br c k]
    exact ss'_clo_bind (R0 := fun _ _ => True) (.step hR)
      (ssim_pure _ _ (hh c s) fun x => .val x PUnit.unit trivial)
      fun xs _ _ => step_ss'_br_r xs.1 (step_ss'_guard_l (CIH (k xs.1, xs.2)))

end CTree
