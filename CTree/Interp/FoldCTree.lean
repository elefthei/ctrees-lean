/- SPDX-License-Identifier: MIT -/
module

public import CTree.Interp.Fold
public import CTree.Eq.Epsilon

/-!
# Folding a choice tree into a choice tree

`fold_ctree h g` is `foldM h g` specialised to `M := CTree F D`, where the guarded `CTree.iter`
inserts a `guard` after every handled node (← `Interp/FoldCTree.v`). Structural equality is `=`,
so the `Proper (equ …)` instances `fold_ctree_equ`, `interp_equ`, `refine_equ` are not needed.
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)
open Coinduction

variable {E F C D : Effect.{u}} {X Y : Type u}

section WithParams
variable (h : (e : E.I) → CTree F D (E.O e)) (g : (c : C.I) → CTree F D (C.O c))

/-- `foldM` into `CTree F D`. -/
def fold_ctree : CTree E C X → CTree F D X := foldM h g

theorem unfold_fold_ctree (t : CTree E C X) :
    fold_ctree h g t = match t.unfold with
      | .ret r => pure r
      | .stuck => .stuck
      | .guard t => .guard (fold_ctree h g t)
      | .step t => .step (.guard (fold_ctree h g t))
      | .vis e k => h e >>= fun x => .guard (fold_ctree h g (k x))
      | .br c k => g c >>= fun x => .guard (fold_ctree h g (k x)) := by
  rw [fold_ctree, foldM, iter_eq, unfold_iter]
  cases t <;> simp [foldStep, mstuck, mstep]

@[simp] theorem fold_ctree_ret (x : X) : fold_ctree h g (pure x : CTree E C X) = pure x := by
  rw [unfold_fold_ctree]; simp
@[simp] theorem fold_ctree_vis (e : E.I) (k : E.O e → CTree E C X) :
    fold_ctree h g (.vis e k) = h e >>= fun x => .guard (fold_ctree h g (k x)) := by
  rw [unfold_fold_ctree]; simp
@[simp] theorem fold_ctree_stuck : fold_ctree h g (.stuck : CTree E C X) = .stuck := by
  rw [unfold_fold_ctree]; simp
@[simp] theorem fold_ctree_guard (t : CTree E C X) :
    fold_ctree h g t.guard = (fold_ctree h g t).guard := by
  rw [unfold_fold_ctree]; simp
@[simp] theorem fold_ctree_step (t : CTree E C X) :
    fold_ctree h g t.step = (fold_ctree h g t).guard.step := by
  rw [unfold_fold_ctree]; simp
@[simp] theorem fold_ctree_br (c : C.I) (k : C.O c → CTree E C X) :
    fold_ctree h g (.br c k) = g c >>= fun x => .guard (fold_ctree h g (k x)) := by
  rw [unfold_fold_ctree]; simp

/-! ## `interp` -/

section Interp
variable [C -< D]

theorem interp_eq_fold_ctree (t : CTree E C X) : interp h t = fold_ctree h mbr t := rfl

theorem unfold_interp (t : CTree E C X) :
    interp h t = match t.unfold with
      | .ret r => pure r
      | .stuck => .stuck
      | .guard t => .guard (interp h t)
      | .step t => .step (.guard (interp h t))
      | .vis e k => h e >>= fun x => .guard (interp h (k x))
      | .br c k => mbr c >>= fun x => .guard (interp h (k x)) :=
  unfold_fold_ctree h mbr t

@[simp] theorem interp_ret (x : X) : interp h (pure x : CTree E C X) = pure x :=
  fold_ctree_ret h mbr x
@[simp] theorem interp_stuck : interp h (.stuck : CTree E C X) = .stuck :=
  fold_ctree_stuck h mbr
@[simp] theorem interp_vis (e : E.I) (k : E.O e → CTree E C X) :
    interp h (.vis e k) = h e >>= fun x => .guard (interp h (k x)) :=
  fold_ctree_vis h mbr e k
@[simp] theorem interp_guard (t : CTree E C X) : interp h t.guard = (interp h t).guard :=
  fold_ctree_guard h mbr t
@[simp] theorem interp_step (t : CTree E C X) : interp h t.step = (interp h t).guard.step :=
  fold_ctree_step h mbr t
theorem interp_br (c : C.I) (k : C.O c → CTree E C X) :
    interp h (.br c k) = mbr c >>= fun x => .guard (interp h (k x)) :=
  fold_ctree_br h mbr c k
@[simp] theorem interp_br' (c : C.I) (k : C.O c → CTree E C X) :
    interp h (.br c k) = .br' c fun x => .guard (interp h (k x)) := by
  rw [interp_br]; simp [mbr, CTree.branch']

end Interp

/-! ## `refine` -/

section Refine
variable [E -< F]

theorem refine_eq_fold_ctree (t : CTree E C X) : refine g t = fold_ctree mtrigger g t := rfl

theorem unfold_refine (t : CTree E C X) :
    refine g t = match t.unfold with
      | .ret r => pure r
      | .stuck => .stuck
      | .guard t => .guard (refine g t)
      | .step t => .step (.guard (refine g t))
      | .vis e k => mtrigger e >>= fun x => .guard (refine g (k x))
      | .br c k => g c >>= fun x => .guard (refine g (k x)) :=
  unfold_fold_ctree mtrigger g t

@[simp] theorem refine_ret (x : X) : refine g (pure x : CTree E C X) = pure x :=
  fold_ctree_ret mtrigger g x
@[simp] theorem refine_vis (e : E.I) (k : E.O e → CTree E C X) :
    refine g (.vis e k) = mtrigger e >>= fun x => .guard (refine g (k x)) :=
  fold_ctree_vis mtrigger g e k
@[simp] theorem refine_guard (t : CTree E C X) : refine g t.guard = (refine g t).guard :=
  fold_ctree_guard mtrigger g t
@[simp] theorem refine_step (t : CTree E C X) : refine g t.step = (refine g t).guard.step :=
  fold_ctree_step mtrigger g t
@[simp] theorem refine_br (c : C.I) (k : C.O c → CTree E C X) :
    refine g (.br c k) = g c >>= fun x => .guard (refine g (k x)) :=
  fold_ctree_br mtrigger g c k

theorem refine_trigger (e : E.I) :
    refine g (CTree.trigger e : CTree E C (E.O e)) ~ (mtrigger e : CTree F D (E.O e)) := by
  rw [CTree.trigger, refine_vis]
  conv => rhs; rw [← bind_pure (mtrigger e : CTree F D (E.O e))]
  exact sbisim_bind_eq _ fun x => by simpa using sb_guard (pure x : CTree F D (E.O e))

end Refine

end WithParams

theorem interp_trigger [C -< D] (h : (e : E.I) → CTree F D (E.O e)) (e : E.I) :
    interp h (CTree.trigger e : CTree E C (E.O e)) = h e >>= fun x => .guard (pure x) := by
  simp [CTree.trigger]

/-! ## Bind -/

theorem fold_ctree_bind (h : (e : E.I) → CTree F D (E.O e)) (g : (c : C.I) → CTree F D (C.O c))
    (t : CTree E C X) (k : X → CTree E C Y) :
    fold_ctree h g (t >>= k) = fold_ctree h g t >>= fun x => fold_ctree h g (k x) := by
  let K := fun x => fold_ctree h g (k x)
  -- bisimulation up to a common prefix `u` in `CTree F D`
  let R : CTree F D Y → CTree F D Y → Prop := fun a b =>
    ∃ (Z : Type u) (u : CTree F D Z) (s : Z → CTree E C X),
      a = u >>= (fun z => fold_ctree h g (s z >>= k)) ∧ b = u >>= fun z => fold_ctree h g (s z) >>= K
  have hc : ∀ (Z : Type u) (u : CTree F D Z) (s : Z → CTree E C X), (∀ z, u ≠ pure z) →
      EqF (fun a b => R a b ∨ a = b) (u >>= fun z => fold_ctree h g (s z >>= k)).unfold
        (u >>= fun z => fold_ctree h g (s z) >>= K).unfold := by
    intro Z u s hu
    cases u with
    | ret z => exact absurd rfl (hu z)
    | stuck => simpa using EqF.stuck
    | step u =>
      simp only [step_bind, unfold_step]; exact .step (.inl ⟨_, u, s, rfl, rfl⟩)
    | guard u =>
      simp only [guard_bind, unfold_guard]; exact .guard (.inl ⟨_, u, s, rfl, rfl⟩)
    | vis e k' =>
      simp only [vis_bind, unfold_vis]; exact .vis e fun x => .inl ⟨_, k' x, s, rfl, rfl⟩
    | br c k' =>
      simp only [br_bind, unfold_br]; exact .br c fun x => .inl ⟨_, k' x, s, rfl, rfl⟩
  have hg : ∀ (W : Type u) (v : CTree F D W) (k' : W → CTree E C X) (z : CTree E C X),
      (v >>= fun x => (pure (k' x) : CTree F D _).guard) ≠ pure z := by
    intro W v k' z hv
    obtain ⟨_, _, hk⟩ := pure_eq_bind_inv hv
    exact absurd (congrArg CTree.unfold hk) (by simp)
  refine eq_coind_upto R ?_ _ _ ⟨_, pure t, id, by simp, by simp [K]⟩
  rintro _ _ ⟨Z, u, s, rfl, rfl⟩
  by_cases hu : ∃ z, u = pure z
  · obtain ⟨z, rfl⟩ := hu
    simp only [pure_bind']
    cases s z with
    | ret x => simpa [K] using EqF.refl (fun _ => .inr rfl) _
    | stuck => simpa using EqF.stuck
    | step t' =>
      simp only [step_bind, fold_ctree_step, guard_bind, unfold_step]
      exact .step (.inl ⟨_, CTree.guard (pure t' : CTree F D (CTree E C X)), id, by simp, by simp⟩)
    | guard t' =>
      simp only [guard_bind, fold_ctree_guard, unfold_guard]
      exact .guard (.inl ⟨_, pure t', id, by simp, by simp⟩)
    | vis e k' =>
      have := hc _ (h e >>= fun x => CTree.guard (pure (k' x) : CTree F D (CTree E C X))) id
        (fun z => hg _ _ _ z)
      simpa [K] using this
    | br c k' =>
      have := hc _ (g c >>= fun x => CTree.guard (pure (k' x) : CTree F D (CTree E C X))) id
        (fun z => hg _ _ _ z)
      simpa [K] using this
  · exact hc Z u s fun z hz => hu ⟨z, hz⟩

theorem interp_bind [C -< D] (h : (e : E.I) → CTree F D (E.O e)) (t : CTree E C X)
    (k : X → CTree E C Y) : interp h (t >>= k) = interp h t >>= fun x => interp h (k x) :=
  fold_ctree_bind h mbr t k

theorem refine_bind [E -< F] (g : (c : C.I) → CTree F D (C.O c)) (t : CTree E C X)
    (k : X → CTree E C Y) : refine g (t >>= k) = refine g t >>= fun x => refine g (k x) :=
  fold_ctree_bind mtrigger g t k

/-! ## Counter-example: `interp` does not preserve `sbisim` -/

namespace CounterExample

/-- The effect with a single event that never answers (Rocq `VoidE`). -/
abbrev VoidE : Effect.{0} := ⟨PUnit, fun _ => PEmpty⟩

def t1 : CTree VoidE B2 Nat := pure 1
def t2 : CTree VoidE B2 Nat :=
  .br2 (pure 1) (CTree.trigger (E := VoidE) ⟨⟩ >>= fun x => nomatch x)

example : t1 ~ t2 := by
  refine sbisim_symm (sbisim_trans (br2_commut _ _) (br2_isStuck ?_ _))
  intro l u hu
  simp only [CTree.trigger] at hu; rw [vis_bind] at hu
  obtain ⟨x, _⟩ := trans_vis_inv hu
  exact (x : PEmpty).elim

def h : (e : VoidE.I) → CTree VoidE B2 (VoidE.O e) := fun _ => .step .stuck

theorem interpE_sbsisim_counterexample : ¬ (interp h t1 ~ interp h t2) := by
  intro hs
  have ht : trans .tau (interp h t2) (CTree.stuck : CTree VoidE B2 Nat) := by
    simp only [t2, CTree.br2, CTree.br']
    rw [interp_br']
    refine trans_br' (B₁ := B2) (.up false) (trans_guard ?_)
    simp [CTree.trigger, Subeffect.map, h]
    exact trans_step _
  obtain ⟨_, ht'⟩ := sbisim_trans_r hs ht
  simp only [t1, interp_ret] at ht'
  cases (trans_ret_inv ht').2

end CounterExample

/-! ## `interp` and internal paths (`M := CTree F C`) -/

section EpsilonInterp
variable (h : (e : E.I) → CTree F C (E.O e))

theorem interp_productive (t : CTree E C X) (hp : Productive (interp h t)) : Productive t := by
  cases t with
  | ret r => exact .ret r
  | stuck => exact absurd (by simpa using hp) productive_stuck
  | step t => exact .step t
  | guard t => exact absurd (by simpa using hp) (productive_guard _)
  | vis e k => exact .vis e k
  | br c k => exact absurd (by simpa [CTree.br'] using hp) (productive_br _ _)

theorem epsilon_interp {t t' : CTree E C X} (hε : Epsilon t t') :
    Epsilon (interp h t) (interp h t') := by
  induction hε with
  | refl => exact .refl _
  | br x _ ih => rw [interp_br']; simp only [CTree.br']; exact .br _ (.guard ih)
  | guard _ ih => rw [interp_guard]; exact .guard ih

theorem interp_ret_inv (t : CTree E C X) (r : X) (he : interp h t = pure r) : t = pure r := by
  cases t with
  | ret x => simpa using he
  | vis e k =>
    obtain ⟨_, _, hk⟩ := pure_eq_bind_inv (by simpa using he)
    exact absurd (congrArg CTree.unfold hk) (by simp)
  | br c k => exact absurd (congrArg CTree.unfold he) (by simp [CTree.br'])
  | _ => exact absurd (congrArg CTree.unfold he) (by simp)

theorem trans_val_interp {t u : CTree E C X} {v : X} (ht : trans (.val v) t u) :
    trans (.val v) (interp h t) .stuck := by
  obtain ⟨hε, -⟩ := trans_val_epsilon ht
  exact epsilon_trans (epsilon_interp h hε) (by simpa using trans_ret v)

theorem trans_tau_interp {t u : CTree E C X} (ht : trans .tau t u) :
    trans .tau (interp h t) (interp h u).guard := by
  obtain ⟨_, hε, rfl⟩ := trans_τ_epsilon ht
  exact epsilon_trans (epsilon_interp h hε) (by simpa using trans_step _)

theorem trans_obs_interp_step {t u : CTree E C X} {u' : CTree F C (E.O e)} {x : E.O e}
    {l : Label F} (ht : trans (.obs e x) t u) (hh : trans l (h e) u') (hl : ¬ IsVal l)
    (hd : EpsilonDet u' (pure x)) :
    trans l (interp h t) (u' >>= fun _ => (interp h u).guard) := by
  obtain ⟨k, hε, rfl⟩ := trans_obs_epsilon ht
  have := epsilon_interp h hε
  rw [interp_vis] at this
  rw [← epsilon_det_bind_ret_l_equ (k := fun x => (interp h (k x)).guard) hd]
  exact epsilon_trans this (trans_bind_l hl hh)

theorem trans_obs_interp_pure {t u : CTree E C X} {x : E.O e} (ht : trans (.obs e x) t u)
    (hh : trans (.val x) (h e) .stuck) : Epsilon (interp h t) (interp h u).guard := by
  obtain ⟨k, hε, rfl⟩ := trans_obs_epsilon ht
  have := epsilon_interp h hε
  rw [interp_vis] at this
  exact this.trans (epsilon_bind_ret (trans_val_epsilon hh).1)

end EpsilonInterp

theorem bind_guard_r {E B : Effect.{u}} (t : CTree E B X) (k : X → CTree E B Y) :
    (t >>= fun x => (k x).guard) = (t >>= fun x => (pure x : CTree E B X).guard) >>= k := by
  simp

end CTree
