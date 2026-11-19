/- SPDX-License-Identifier: MIT -/
module

public import CTree.Interp.Recursion
public import CTree.Interp.FoldCTree
public import CTree.Eq.SBisimAlt

/-!
# Properties of `mrec` and `rec` (← `Interp/RecursionFacts.v`)

`interp_mrec ctx` unfolds node by node (`unfold_interp_mrec`), commutes with `>>=`
(`interp_mrec_bind`), and is strongly bisimilar to `interp (mrecursive ctx)`
(`interp_mrec_as_interp`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)

open CTree.Coinduction
variable {D E B : Effect.{u}} {R S : Type u}

section Facts
variable (ctx : (d : D.I) → CTree (D ⊕ₑ E) B (D.O d))

/-- One unfolding step of `interp_mrec ctx`. -/
def _interp_mrec : CTreeF (D ⊕ₑ E) B R (CTree (D ⊕ₑ E) B R) → CTree E B R
  | .ret r => pure r
  | .stuck => .stuck
  | .step t => .step (.guard (interp_mrec ctx t))
  | .guard t => .guard (interp_mrec ctx t)
  | .vis (.inl d) k => .guard (interp_mrec ctx (ctx d >>= k))
  | .vis (.inr e) k => .vis e fun x => .guard (interp_mrec ctx (k x))
  | .br c k => .br c fun x => .guard (interp_mrec ctx (k x))

theorem unfold_interp_mrec (t : CTree (D ⊕ₑ E) B R) :
    interp_mrec ctx t = _interp_mrec ctx t.unfold := by
  rw [interp_mrec, unfold_iter]
  cases t with
  | vis e k => cases e <;> simp [_interp_mrec] <;> rfl
  | _ => simp [_interp_mrec] <;> rfl

@[simp] theorem interp_mrec_ret (r : R) : interp_mrec ctx (pure r : CTree (D ⊕ₑ E) B R) = pure r := by
  rw [unfold_interp_mrec]; simp [_interp_mrec]
@[simp] theorem interp_mrec_stuck : interp_mrec ctx (.stuck : CTree (D ⊕ₑ E) B R) = .stuck := by
  rw [unfold_interp_mrec]; simp [_interp_mrec]
@[simp] theorem interp_mrec_step (t : CTree (D ⊕ₑ E) B R) :
    interp_mrec ctx t.step = .step (.guard (interp_mrec ctx t)) := by
  rw [unfold_interp_mrec]; simp [_interp_mrec]
@[simp] theorem interp_mrec_guard_eq (t : CTree (D ⊕ₑ E) B R) :
    interp_mrec ctx t.guard = .guard (interp_mrec ctx t) := by
  rw [unfold_interp_mrec]; simp [_interp_mrec]
@[simp] theorem interp_mrec_vis_inl (d : D.I) (k : D.O d → CTree (D ⊕ₑ E) B R) :
    interp_mrec ctx (.vis (E := D ⊕ₑ E) (.inl d) k) = .guard (interp_mrec ctx (ctx d >>= k)) := by
  rw [unfold_interp_mrec]; simp [_interp_mrec]
@[simp] theorem interp_mrec_vis_inr (e : E.I) (k : E.O e → CTree (D ⊕ₑ E) B R) :
    interp_mrec ctx (.vis (E := D ⊕ₑ E) (.inr e) k) =
      .vis e fun x => .guard (interp_mrec ctx (k x)) := by
  rw [unfold_interp_mrec]; simp [_interp_mrec]
@[simp] theorem interp_mrec_br (c : B.I) (k : B.O c → CTree (D ⊕ₑ E) B R) :
    interp_mrec ctx (.br c k) = .br c fun x => .guard (interp_mrec ctx (k x)) := by
  rw [unfold_interp_mrec]; simp [_interp_mrec]

/-- The handler of `D ⊕ₑ E` that runs `D` calls with `mrec ctx` and re-emits `E` events. -/
def mrecursive : (e : (D ⊕ₑ E).I) → CTree E B ((D ⊕ₑ E).O e)
  | .inl d => mrec ctx d
  | .inr e => CTree.trigger e

theorem interp_mrec_bind (t : CTree (D ⊕ₑ E) B R) (k : R → CTree (D ⊕ₑ E) B S) :
    interp_mrec ctx (t >>= k) = interp_mrec ctx t >>= fun x => interp_mrec ctx (k x) := by
  -- pairs related directly or under one `guard` (the one `interp_mrec` adds before children)
  refine eq_coind_upto (fun a b => ∃ (T : Type u) (t : CTree (D ⊕ₑ E) B T) (k : T → _),
      (a = interp_mrec ctx (t >>= k) ∧ b = interp_mrec ctx t >>= fun x => interp_mrec ctx (k x)) ∨
      (a = .guard (interp_mrec ctx (t >>= k)) ∧
        b = .guard (interp_mrec ctx t >>= fun x => interp_mrec ctx (k x))))
    ?_ _ _ ⟨R, t, k, .inl ⟨rfl, rfl⟩⟩
  rintro _ _ ⟨T, t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · cases t with
    | ret r => simp; exact EqF.refl (fun _ => .inr rfl) _
    | stuck => simp; exact .stuck
    | step t => simp; exact .step (.inl ⟨T, t, k, .inr ⟨rfl, rfl⟩⟩)
    | guard t => simp; exact .guard (.inl ⟨T, t, k, .inl ⟨rfl, rfl⟩⟩)
    | vis e h =>
      cases e with
      | inl d => simp; exact .guard (.inl ⟨T, ctx d >>= h, k, .inl ⟨by simp, rfl⟩⟩)
      | inr e => simp; exact .vis _ fun x => .inl ⟨T, h x, k, .inr ⟨rfl, rfl⟩⟩
    | br c h => simp; exact .br _ fun x => .inl ⟨T, h x, k, .inr ⟨rfl, rfl⟩⟩
  · simp; exact .guard (.inl ⟨T, t, k, .inl ⟨rfl, rfl⟩⟩)

theorem interp_mrec_trigger (a : (D ⊕ₑ E).I) :
    interp_mrec ctx (CTree.trigger a : CTree (D ⊕ₑ E) B _) ≲ mrecursive ctx a := by
  cases a with
  | inl d =>
    simp only [CTree.trigger, interp_mrec_vis_inl, bind_pure, mrecursive, mrec]
    exact ssim_guard_l (ssim_refl (fun _ => rfl) _)
  | inr e =>
    simp only [CTree.trigger, interp_mrec_vis_inr, interp_mrec_ret, mrecursive]
    exact ssim_vis_id e e rfl _ _ fun x => ⟨ssim_guard_l (ssim_refl (fun _ => rfl) _), rfl⟩

theorem interp_mrec_guard (c : CTree (D ⊕ₑ E) B R) :
    CTree.guard (interp_mrec ctx c) ~ interp_mrec ctx (.guard c) := by
  rw [interp_mrec_guard_eq]; exact sbisim_refl _

theorem interp_mrec_as_interp (c : CTree (D ⊕ₑ E) B R) :
    interp_mrec ctx c ~ interp (mrecursive ctx) c := by
  -- as in Rocq: relate `interp_mrec ctx c` to `guard (interp … c)`, then drop the guard
  suffices h : ∀ c : CTree (D ⊕ₑ E) B R, ∀ side,
      gfp (sb' Eq) side (interp_mrec ctx c) (.guard (interp (mrecursive ctx) c)) from
    sbisim_trans (sbisim_sbisim'.2 (h c)) (sb_guard _)
  refine gfp_prop (b := sb' Eq) (P := fun Rr => ∀ (c : CTree (D ⊕ₑ E) B R) side,
      Rr side (interp_mrec ctx c) (.guard (interp (mrecursive ctx) c)))
    (tower (infClosed_forall fun c => infClosed_forall fun s => Rel3.infClosed_apply s _ _) ?_)
  intro Rr hR CIH c side
  cases c with
  | ret r =>
    simp only [interp_mrec_ret, interp_ret]
    exact step_sb'_guard_r hR (step_sb'_ret rfl (fun s => b_chain hR s _ _ (sb'_stuck s)) side)
  | stuck =>
    simp only [interp_mrec_stuck, interp_stuck]
    exact step_sb'_guard_r hR (sb'_stuck side)
  | step t =>
    simp only [interp_mrec_step, interp_step]
    exact step_sb'_guard_r hR
      (step_sb'_step rfl (step_sb'_guard_l' hR fun s => CIH t s) side)
  | guard t =>
    simp only [interp_mrec_guard_eq, interp_guard]
    exact step_sb'_guard (CIH t side)
  | vis e k =>
    cases e with
    | inl d =>
      simp only [interp_mrec_vis_inl, interp_vis, interp_mrec_bind, mrecursive, mrec]
      exact step_sb'_guard (st'_clo_bind_eq hR (sbisim_gfp_sb' (sbisim_refl _))
        fun x s => CIH (k x) s)
    | inr e =>
      simp only [interp_mrec_vis_inr, interp_vis, mrecursive, CTree.trigger, vis_bind,
        LawfulMonad.pure_bind]
      exact step_sb'_guard_r hR (step_sb'_vis_id rfl
        (fun x => ⟨step_sb'_guard_l' hR fun s => CIH (k x) s, rfl⟩) side)
  | br c k =>
    simp only [interp_mrec_br, interp_br']
    exact step_sb'_guard_r hR
      (step_sb'_br_id rfl fun x => step_sb'_guard_l' hR (fun s => CIH (k x) s) side)

theorem mrec_as_interp (d : D.I) : mrec ctx d ~ interp (mrecursive ctx) (ctx d) :=
  interp_mrec_as_interp ctx (ctx d)

/-- `interp h (trigger e)` is `guard (h e)` up to `~` (Rocq `RecursionFacts.interp_trigger`;
the equation `interp_trigger` lives in `FoldCTree`). -/
theorem interp_trigger_sbisim {E' F' B' : Effect.{u}} (h : (e : E'.I) → CTree F' B' (E'.O e))
    (e : E'.I) : interp h (CTree.trigger e : CTree E' B' (E'.O e)) ~ CTree.guard (h e) := by
  rw [interp_trigger]
  refine sbisim_trans (sbisim_bind_eq _ fun x => sb_guard _) ?_
  rw [bind_pure]; exact sbisim_symm (sb_guard _)

theorem interp_mrecursive (d : D.I) :
    interp (mrecursive ctx) (trigger_inl1 (E := E) (B := B) d) ~ mrec ctx d :=
  sbisim_trans (interp_trigger_sbisim _ _) (sb_guard _)

end Facts

section RecursiveFacts
variable {X Y : Type u} (f : X → CTree (callE X Y ⊕ₑ E) B Y)

/-- The handler of `callE X Y ⊕ₑ E` that runs calls with `rec f`. -/
def recursive : (e : (callE X Y ⊕ₑ E).I) → CTree E B ((callE X Y ⊕ₑ E).O e)
  | .inl x => calling (rec f) x
  | .inr e => CTree.trigger e

theorem interp_recursive_call (x : X) : interp (recursive f) (call x : CTree _ B Y) ~ rec f x :=
  sbisim_trans (interp_trigger_sbisim _ _) (sb_guard _)

end RecursiveFacts

end CTree
