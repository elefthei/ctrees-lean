/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.Trans

/-!
# Scheduling head of choice trees

`head t` is the prefix of `t` made of `br` and `guard` nodes. Each of its leaves returns the next
observable action of `t` (`HAction`): a return, a `step` with its continuation, or a visible event
with its continuation. The transitions of `t` are exactly the `val` transitions of `head t`.
`head t` loops if `t` has an infinite path of `br`/`guard` nodes (← `Misc/Head.v`).

Structural equality is `=`, so Rocq's `eq_haction` (which lifts `equ` to actions) and `head_equ`
are not needed.
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)

/-- The next observable action of a tree. -/
inductive HAction (E B : Effect.{u}) (X : Type u) : Type u
  | ret (r : X)
  | step (t : CTree E B X)
  | vis (e : E.I) (k : E.O e → CTree E B X)

variable {E F B C : Effect.{u}} {X : Type u}

section Head
variable [B -< C]

/-- Scrolls `t` through its `br` and `guard` nodes until reaching an observable node. -/
def head (t : CTree E B X) : CTree F C (HAction E B X) :=
  match t.unfold with
  | .ret x => pure (.ret x)
  | .stuck => .stuck
  | .step t => pure (.step t)
  | .guard t => .guard (head t)
  | .vis e k => pure (.vis e k)
  | .br c k => .br' c fun x => head (k x)
partial_fixpoint

theorem unfold_head (t : CTree E B X) :
    (head t : CTree F C (HAction E B X)) = match t.unfold with
      | .ret x => pure (.ret x)
      | .stuck => .stuck
      | .step t => pure (.step t)
      | .guard t => .guard (head t)
      | .vis e k => pure (.vis e k)
      | .br c k => .br' c fun x => head (k x) := by
  rw [head]

@[simp] theorem head_pure (x : X) :
    (head (pure x : CTree E B X) : CTree F C (HAction E B X)) = pure (.ret x) := by
  rw [unfold_head]; simp
@[simp] theorem head_stuck :
    (head (.stuck : CTree E B X) : CTree F C (HAction E B X)) = .stuck := by
  rw [unfold_head]; simp
@[simp] theorem head_step (t : CTree E B X) :
    (head t.step : CTree F C (HAction E B X)) = pure (.step t) := by
  rw [unfold_head]; simp
@[simp] theorem head_guard (t : CTree E B X) :
    (head t.guard : CTree F C (HAction E B X)) = .guard (head t) := by
  rw [unfold_head]; simp
@[simp] theorem head_vis (e : E.I) (k : E.O e → CTree E B X) :
    (head (.vis e k) : CTree F C (HAction E B X)) = pure (.vis e k) := by
  rw [unfold_head]; simp
@[simp] theorem head_br (c : B.I) (k : B.O c → CTree E B X) :
    (head (.br c k) : CTree F C (HAction E B X)) = .br' c fun x => head (k x) := by
  rw [unfold_head]; simp

/-! ## Transitions of a tree are reflected in its head -/

section TransHead
variable [LawfulSubeffect B C] {t u : CTree E B X}

theorem trans_head_obs {e : E.I} {v : E.O e} (h : trans (.obs e v) t u) :
    ∃ k, trans (.val (HAction.vis e k)) (head t : CTree F C (HAction E B X)) .stuck ∧ u = k v := by
  unfold trans at h
  generalize hl : Label.obs e v = l at h
  generalize ht : t.unfold = T at h
  induction h generalizing t with
  | @br c x k' l u _ ih =>
    cases t with
    | br c₀ k₀ =>
      simp only [unfold_br] at ht; cases ht
      obtain ⟨k, h, rfl⟩ := ih hl rfl
      exact ⟨k, by simpa using trans_br' x h, rfl⟩
    | _ => simp at ht
  | @guard t₁ t' l _ ih =>
    cases t with
    | guard t₀ =>
      simp only [unfold_guard] at ht; cases ht
      obtain ⟨k, h, rfl⟩ := ih hl rfl
      exact ⟨k, by simpa using trans_guard h, rfl⟩
    | _ => simp at ht
  | step => cases hl
  | @obs e' k' x =>
    cases hl
    cases t with
    | vis e₀ k₀ =>
      simp only [unfold_vis] at ht; cases ht
      exact ⟨k', by simpa using trans_ret (HAction.vis e k'), rfl⟩
    | _ => simp at ht
  | val => cases hl

theorem trans_head_tau (h : trans .tau t u) :
    trans (.val (HAction.step u)) (head t : CTree F C (HAction E B X)) .stuck := by
  unfold trans at h
  generalize hl : (Label.tau : Label E) = l at h
  generalize ht : t.unfold = T at h
  induction h generalizing t with
  | @br c x k' l u _ ih =>
    cases t with
    | br c₀ k₀ =>
      simp only [unfold_br] at ht; cases ht
      simpa using trans_br' x (ih hl rfl)
    | _ => simp at ht
  | @guard t₁ t' l _ ih =>
    cases t with
    | guard t₀ =>
      simp only [unfold_guard] at ht; cases ht
      simpa using trans_guard (ih hl rfl)
    | _ => simp at ht
  | @step t₁ =>
    cases t with
    | step t₀ =>
      simp only [unfold_step] at ht; cases ht
      simpa using trans_ret (HAction.step t₁)
    | _ => simp at ht
  | obs => cases hl
  | val => cases hl

theorem trans_head_ret {v : X} (h : trans (.val v) t u) :
    trans (.val (HAction.ret v : HAction E B X)) (head t : CTree F C (HAction E B X)) .stuck ∧
      u = .stuck := by
  unfold trans at h
  generalize hl : (Label.val v : Label E) = l at h
  generalize ht : t.unfold = T at h
  induction h generalizing t with
  | @br c x k' l u _ ih =>
    cases t with
    | br c₀ k₀ =>
      simp only [unfold_br] at ht; cases ht
      obtain ⟨h, rfl⟩ := ih hl rfl
      exact ⟨by simpa using trans_br' x h, rfl⟩
    | _ => simp at ht
  | @guard t₁ t' l _ ih =>
    cases t with
    | guard t₀ =>
      simp only [unfold_guard] at ht; cases ht
      obtain ⟨h, rfl⟩ := ih hl rfl
      exact ⟨by simpa using trans_guard h, rfl⟩
    | _ => simp at ht
  | step => cases hl
  | obs => cases hl
  | @val r =>
    cases val_eq_inv hl
    cases t with
    | ret r₀ =>
      simp only [unfold_pure] at ht; cases ht
      exact ⟨by simpa using trans_ret (HAction.ret v : HAction E B X), rfl⟩
    | _ => simp at ht

/-- The three cases of `trans_head_obs`, `trans_head_tau`, `trans_head_ret`, by label. -/
theorem trans_head {l : Label E} (h : trans l t u) :
    match l with
    | .tau => trans (.val (HAction.step u)) (head t : CTree F C (HAction E B X)) .stuck
    | .obs e v => ∃ k, trans (.val (HAction.vis e k)) (head t : CTree F C (HAction E B X)) .stuck ∧
        u = k v
    | @Label.val _ _ v => trans (.val (HAction.ret (E := E) (B := B) v))
        (head t : CTree F C (HAction E B X)) .stuck ∧ u = .stuck := by
  match l, h with
  | .tau, h => exact trans_head_tau h
  | .obs _ _, h => exact trans_head_obs h
  | .val _, h => cases trans_val_invT h; exact trans_head_ret h

end TransHead

/-! ## Transitions of the head are reflected in the tree -/

section HeadTrans
variable {p : CTree E B X} {q : CTree F C (HAction E B X)}

/-- The head of a tree only takes `val` transitions. -/
theorem trans_head_inv {l : Label F} (h : trans l (head p : CTree F C (HAction E B X)) q) :
    IsVal l := by
  unfold trans at h
  generalize ht : (head p : CTree F C (HAction E B X)).unfold = T at h
  induction h generalizing p with
  | br x _ ih =>
    cases p with
    | br c₀ k₀ => simp only [head_br, CTree.br', unfold_br] at ht; cases ht; exact ih rfl
    | _ => simp at ht
  | guard _ ih =>
    cases p with
    | guard t₀ => simp only [head_guard, unfold_guard] at ht; cases ht; exact ih rfl
    | _ => simp [CTree.br'] at ht
  | step => cases p <;> simp [CTree.br'] at ht
  | obs => cases p <;> simp [CTree.br'] at ht
  | val => exact .val _

theorem trans_ARet {r : X} (h : trans (.val (HAction.ret r : HAction E B X))
    (head p : CTree F C (HAction E B X)) q) : trans (.val r) p .stuck := by
  unfold trans at h
  generalize hl : (Label.val (HAction.ret r : HAction E B X) : Label F) = l at h
  generalize ht : (head p : CTree F C (HAction E B X)).unfold = T at h
  induction h generalizing p with
  | br x _ ih =>
    cases p with
    | br c₀ k₀ =>
      simp only [head_br, CTree.br', unfold_br] at ht; cases ht; exact trans_br _ (ih hl rfl)
    | _ => simp at ht
  | guard _ ih =>
    cases p with
    | guard t₀ =>
      simp only [head_guard, unfold_guard] at ht; cases ht; exact trans_guard (ih hl rfl)
    | _ => simp [CTree.br'] at ht
  | step => cases hl
  | obs => cases hl
  | val =>
    cases val_eq_inv hl
    cases p with
    | ret r₀ => simp at ht; cases ht; exact trans_ret _
    | _ => simp [CTree.br'] at ht

/-- Rocq `trans_ABr`. -/
theorem trans_AStep {u : CTree E B X} (h : trans (.val (HAction.step u))
    (head p : CTree F C (HAction E B X)) q) : trans .tau p u := by
  unfold trans at h
  generalize hl : (Label.val (HAction.step u) : Label F) = l at h
  generalize ht : (head p : CTree F C (HAction E B X)).unfold = T at h
  induction h generalizing p with
  | br x _ ih =>
    cases p with
    | br c₀ k₀ =>
      simp only [head_br, CTree.br', unfold_br] at ht; cases ht; exact trans_br _ (ih hl rfl)
    | _ => simp at ht
  | guard _ ih =>
    cases p with
    | guard t₀ =>
      simp only [head_guard, unfold_guard] at ht; cases ht; exact trans_guard (ih hl rfl)
    | _ => simp [CTree.br'] at ht
  | step => cases hl
  | obs => cases hl
  | val =>
    cases val_eq_inv hl
    cases p with
    | step t₀ => simp at ht; cases ht; exact trans_step _
    | _ => simp [CTree.br'] at ht

theorem trans_AVis {e : E.I} {k : E.O e → CTree E B X} (h : trans (.val (HAction.vis e k))
    (head p : CTree F C (HAction E B X)) q) (i : E.O e) : trans (.obs e i) p (k i) := by
  unfold trans at h
  generalize hl : (Label.val (HAction.vis e k) : Label F) = l at h
  generalize ht : (head p : CTree F C (HAction E B X)).unfold = T at h
  induction h generalizing p with
  | br x _ ih =>
    cases p with
    | br c₀ k₀ =>
      simp only [head_br, CTree.br', unfold_br] at ht; cases ht; exact trans_br _ (ih hl rfl)
    | _ => simp at ht
  | guard _ ih =>
    cases p with
    | guard t₀ =>
      simp only [head_guard, unfold_guard] at ht; cases ht; exact trans_guard (ih hl rfl)
    | _ => simp [CTree.br'] at ht
  | step => cases hl
  | obs => cases hl
  | val =>
    cases val_eq_inv hl
    cases p with
    | vis e₀ k₀ => simp only [head_vis, unfold_pure] at ht; cases ht; exact trans_vis _ _
    | _ => simp [CTree.br'] at ht

end HeadTrans
end Head

/-! ## Running an action -/

/-- Performs the action computed by `head`. -/
def runHAction : HAction E B X → CTree E B X
  | .ret r => pure r
  | .step t => .step t
  | .vis e k => .vis e k

/-- A tree is its head followed by the action it computes. -/
theorem get_run_haction (t : CTree E B X) : t = head t >>= runHAction := by
  refine eq_coind_upto (fun a b => b = head a >>= runHAction) ?_ t _ rfl
  rintro a b rfl
  cases a with
  | ret r => simpa [runHAction] using EqF.ret r
  | stuck => simpa using EqF.stuck
  | step t => simpa [runHAction] using EqF.step (.inr rfl)
  | guard t => simpa using EqF.guard (.inl rfl)
  | vis e k => simpa [runHAction] using EqF.vis e fun _ => .inr rfl
  | br c k => simp [CTree.br']; exact EqF.br c fun _ => .inl rfl

end CTree
