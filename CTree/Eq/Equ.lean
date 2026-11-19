/- SPDX-License-Identifier: MIT -/
module

public import CTree.Core.Definitions

/-!
# Structural equality

Rocq's coinductive structural equality `equ eq` (`≅`) is Lean's `=` on `CTree` (the type is
extensional). This file provides the coinduction principle for equality (`eq_coind`), constructor
mismatch lemmas, and the inversion lemmas of `bind` (← `Eq/Equ.v`, `Eq/Shallow.v`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect)

variable {E B : Effect.{u}} {R X Y : Type u}

/-- One layer of structural equality, relating the children by `R`. -/
inductive EqF (R : CTree E B X → CTree E B X → Prop) :
    CTreeF E B X (CTree E B X) → CTreeF E B X (CTree E B X) → Prop
  | ret (r : X) : EqF R (.ret r) (.ret r)
  | stuck : EqF R .stuck .stuck
  | step {t u} : R t u → EqF R (.step t) (.step u)
  | guard {t u} : R t u → EqF R (.guard t) (.guard u)
  | vis (e : E.I) {k₁ k₂ : E.O e → CTree E B X} :
      (∀ x, R (k₁ x) (k₂ x)) → EqF R (.vis e k₁) (.vis e k₂)
  | br (c : B.I) {k₁ k₂ : B.O c → CTree E B X} :
      (∀ x, R (k₁ x) (k₂ x)) → EqF R (.br c k₁) (.br c k₂)

theorem EqF.mono {R S : CTree E B X → CTree E B X → Prop} (hRS : ∀ t u, R t u → S t u)
    {ot ou : CTreeF E B X (CTree E B X)} (h : EqF R ot ou) : EqF S ot ou := by
  cases h with
  | ret => exact .ret _
  | stuck => exact .stuck
  | step h => exact .step (hRS _ _ h)
  | guard h => exact .guard (hRS _ _ h)
  | vis e h => exact .vis e fun x => hRS _ _ (h x)
  | br c h => exact .br c fun x => hRS _ _ (h x)

theorem EqF.refl {R : CTree E B X → CTree E B X → Prop} (hR : ∀ t, R t t) :
    ∀ ot : CTreeF E B X (CTree E B X), EqF R ot ot
  | .ret r => .ret r
  | .stuck => .stuck
  | .step _ => .step (hR _)
  | .guard _ => .guard (hR _)
  | .vis e _ => .vis e fun _ => hR _
  | .br c _ => .br c fun _ => hR _

/-- Replaces Rocq's `coinduction` for `equ eq`: a bisimulation proves equality. -/
theorem eq_coind (R : CTree E B X → CTree E B X → Prop)
    (h : ∀ t u, R t u → EqF R t.unfold u.unfold) : ∀ t u, R t u → t = u := by
  intro t u hR
  ext n
  induction n generalizing t u with
  | zero => rfl
  | succ n ih =>
    have hF := h t u hR
    rw [← fold_unfold t, ← fold_unfold u]
    generalize t.unfold = ot, u.unfold = ou at hF
    cases hF with
    | ret => rfl
    | stuck => rfl
    | step h => simp [ih _ _ h]
    | guard h => simp [ih _ _ h]
    | vis e h => simp only [fold_vis_approx_1]; congr; funext x; exact ih _ _ (h x)
    | br c h => simp only [fold_br_approx_1]; congr; funext x; exact ih _ _ (h x)

/-- `eq_coind` up to equality. -/
theorem eq_coind_upto (R : CTree E B X → CTree E B X → Prop)
    (h : ∀ t u, R t u → EqF (fun a b => R a b ∨ a = b) t.unfold u.unfold) :
    ∀ t u, R t u → t = u := by
  intro t u hR
  refine eq_coind (fun a b => R a b ∨ a = b) ?_ t u (.inl hR)
  rintro a b (hab | rfl)
  · exact h a b hab
  · exact EqF.refl (fun _ => .inr rfl) _

/-! ## Constructor mismatches -/

section Mismatch
variable {r r' : R} {t t' : CTree E B R} {e e' : E.I} {c c' : B.I}
  {ke : E.O e → CTree E B R} {ke' : E.O e' → CTree E B R}
  {kc : B.O c → CTree E B R} {kc' : B.O c' → CTree E B R}

theorem ne_of_unfold {t u : CTree E B R} (h : t.unfold ≠ u.unfold := by simp) : t ≠ u :=
  fun e => h (e ▸ rfl)

@[simp] theorem pure_ne_stuck : (pure r : CTree E B R) ≠ .stuck := ne_of_unfold
@[simp] theorem pure_ne_step : (pure r : CTree E B R) ≠ .step t' := ne_of_unfold
@[simp] theorem pure_ne_guard : (pure r : CTree E B R) ≠ .guard t' := ne_of_unfold
@[simp] theorem pure_ne_vis : (pure r : CTree E B R) ≠ .vis e' ke' := ne_of_unfold
@[simp] theorem pure_ne_br : (pure r : CTree E B R) ≠ .br c' kc' := ne_of_unfold
@[simp] theorem stuck_ne_pure : (.stuck : CTree E B R) ≠ pure r' := ne_of_unfold
@[simp] theorem stuck_ne_step : (.stuck : CTree E B R) ≠ .step t' := ne_of_unfold
@[simp] theorem stuck_ne_guard : (.stuck : CTree E B R) ≠ .guard t' := ne_of_unfold
@[simp] theorem stuck_ne_vis : (.stuck : CTree E B R) ≠ .vis e' ke' := ne_of_unfold
@[simp] theorem stuck_ne_br : (.stuck : CTree E B R) ≠ .br c' kc' := ne_of_unfold
@[simp] theorem step_ne_pure : (.step t : CTree E B R) ≠ pure r' := ne_of_unfold
@[simp] theorem step_ne_stuck : (.step t : CTree E B R) ≠ .stuck := ne_of_unfold
@[simp] theorem step_ne_guard : (.step t : CTree E B R) ≠ .guard t' := ne_of_unfold
@[simp] theorem step_ne_vis : (.step t : CTree E B R) ≠ .vis e' ke' := ne_of_unfold
@[simp] theorem step_ne_br : (.step t : CTree E B R) ≠ .br c' kc' := ne_of_unfold
@[simp] theorem guard_ne_pure : (.guard t : CTree E B R) ≠ pure r' := ne_of_unfold
@[simp] theorem guard_ne_stuck : (.guard t : CTree E B R) ≠ .stuck := ne_of_unfold
@[simp] theorem guard_ne_step : (.guard t : CTree E B R) ≠ .step t' := ne_of_unfold
@[simp] theorem guard_ne_vis : (.guard t : CTree E B R) ≠ .vis e' ke' := ne_of_unfold
@[simp] theorem guard_ne_br : (.guard t : CTree E B R) ≠ .br c' kc' := ne_of_unfold
@[simp] theorem vis_ne_pure : (.vis e ke : CTree E B R) ≠ pure r' := ne_of_unfold
@[simp] theorem vis_ne_stuck : (.vis e ke : CTree E B R) ≠ .stuck := ne_of_unfold
@[simp] theorem vis_ne_step : (.vis e ke : CTree E B R) ≠ .step t' := ne_of_unfold
@[simp] theorem vis_ne_guard : (.vis e ke : CTree E B R) ≠ .guard t' := ne_of_unfold
@[simp] theorem vis_ne_br : (.vis e ke : CTree E B R) ≠ .br c' kc' := ne_of_unfold
@[simp] theorem br_ne_pure : (.br c kc : CTree E B R) ≠ pure r' := ne_of_unfold
@[simp] theorem br_ne_stuck : (.br c kc : CTree E B R) ≠ .stuck := ne_of_unfold
@[simp] theorem br_ne_step : (.br c kc : CTree E B R) ≠ .step t' := ne_of_unfold
@[simp] theorem br_ne_guard : (.br c kc : CTree E B R) ≠ .guard t' := ne_of_unfold
@[simp] theorem br_ne_vis : (.br c kc : CTree E B R) ≠ .vis e' ke' := ne_of_unfold

@[simp] theorem pure_eq_pure_iff : (pure r : CTree E B R) = pure r' ↔ r = r' := by
  simp [← ret_eq_pure]

theorem vis_eq_vis_iff' : (.vis e ke : CTree E B R) = .vis e' ke' ↔ e = e' ∧ HEq ke ke' := by
  constructor
  · intro h
    have := congrArg CTree.unfold h
    simp only [unfold_vis, CTreeF.vis.injEq] at this
    exact this
  · rintro ⟨rfl, h⟩; cases h; rfl

theorem br_eq_br_iff' : (.br c kc : CTree E B R) = .br c' kc' ↔ c = c' ∧ HEq kc kc' := by
  constructor
  · intro h
    have := congrArg CTree.unfold h
    simp only [unfold_br, CTreeF.br.injEq] at this
    exact this
  · rintro ⟨rfl, h⟩; cases h; rfl

theorem spin_ne_pure : (CTree.spin : CTree E B R) ≠ pure r := by rw [unfold_spin]; simp
theorem spin_ne_stuck : (CTree.spin : CTree E B R) ≠ .stuck := by rw [unfold_spin]; simp
theorem spinS_ne_pure : (CTree.spinS : CTree E B R) ≠ pure r := by rw [unfold_spinS]; simp
theorem spinS_ne_stuck : (CTree.spinS : CTree E B R) ≠ .stuck := by rw [unfold_spinS]; simp

end Mismatch

/-! ## Equations of atomic trees -/

@[simp] theorem bind_trigger (e : E.I) (k : E.O e → CTree E B Y) :
    CTree.trigger e >>= k = .vis e k := by
  simp [CTree.trigger]

@[simp] theorem bind_branch (c : B.I) (k : B.O c → CTree E B Y) :
    CTree.branch c >>= k = .br c k := by
  simp [CTree.branch]

@[simp] theorem bind_branchS (c : B.I) (k : B.O c → CTree E B Y) :
    CTree.branchS c >>= k = .brS c k := by
  simp [CTree.branchS]

@[simp] theorem bind_trigger' {E₁ : Effect.{u}} [E₁ -< E] (e : E₁.I) (k : E₁.O e → CTree E B Y) :
    CTree.trigger' E₁ e >>= k = .vis' e k := by
  simp [CTree.trigger']

@[simp] theorem bind_branch' {B₁ : Effect.{u}} [B₁ -< B] (c : B₁.I) (k : B₁.O c → CTree E B Y) :
    CTree.branch' B₁ c >>= k = .br' c k := by
  simp [CTree.branch']

@[simp] theorem bind_branchS' {B₁ : Effect.{u}} [B₁ -< B] (c : B₁.I) (k : B₁.O c → CTree E B Y) :
    CTree.branchS' B₁ c >>= k = .brS' c k := by
  simp [CTree.branchS']

@[simp] theorem map_spin (f : X → Y) : f <$> (CTree.spin : CTree E B X) = .spin := by
  simp [← bind_pure_comp]

@[simp] theorem map_spinS (f : X → Y) : f <$> (CTree.spinS : CTree E B X) = .spinS := by
  simp [← bind_pure_comp]

/-! ## Inversion of `bind` -/

section BindInv
variable {t : CTree E B X} {k : X → CTree E B Y}

theorem pure_eq_bind_inv {r : Y} (h : t >>= k = pure r) : ∃ x, t = pure x ∧ k x = pure r := by
  cases t <;> simp_all

theorem stuck_eq_bind_inv (h : t >>= k = .stuck) :
    (∃ x, t = pure x ∧ k x = .stuck) ∨ t = .stuck := by
  cases t <;> simp_all

theorem guard_eq_bind_inv {u : CTree E B Y} (h : t >>= k = .guard u) :
    (∃ x, t = pure x ∧ k x = .guard u) ∨ ∃ t', t = .guard t' ∧ t' >>= k = u := by
  cases t <;> simp_all

theorem step_eq_bind_inv {u : CTree E B Y} (h : t >>= k = .step u) :
    (∃ x, t = pure x ∧ k x = .step u) ∨ ∃ t', t = .step t' ∧ t' >>= k = u := by
  cases t <;> simp_all

theorem vis_eq_bind_inv {e : E.I} {h : E.O e → CTree E B Y} (H : t >>= k = .vis e h) :
    (∃ x, t = pure x ∧ k x = .vis e h) ∨ ∃ k₀, t = .vis e k₀ ∧ ∀ x, h x = k₀ x >>= k := by
  cases t with
  | vis e' k₀ =>
    simp only [vis_bind, vis_eq_vis_iff'] at H
    obtain ⟨rfl, H⟩ := H
    cases H
    exact .inr ⟨k₀, rfl, fun _ => rfl⟩
  | _ => simp_all

theorem br_eq_bind_inv {c : B.I} {h : B.O c → CTree E B Y} (H : t >>= k = .br c h) :
    (∃ x, t = pure x ∧ k x = .br c h) ∨ ∃ k₀, t = .br c k₀ ∧ ∀ x, h x = k₀ x >>= k := by
  cases t with
  | br c' k₀ =>
    simp only [br_bind, br_eq_br_iff'] at H
    obtain ⟨rfl, H⟩ := H
    cases H
    exact .inr ⟨k₀, rfl, fun _ => rfl⟩
  | _ => simp_all

end BindInv

end CTree
