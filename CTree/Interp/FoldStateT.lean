/- SPDX-License-Identifier: MIT -/
module

public import CTree.Interp.Fold
public import CTree.Eq.Epsilon
public import CTree.Interp.FoldCTree
public import CTree.Misc.Pure
public import CTree.Eq.IterFacts

/-!
# Folding into a state monad (← `Interp/FoldStateT.v`)

`fold_state`, `interp_state`, `refine_state` are `foldM`, `interp`, `refine` at the monad
`StateT S M`. Lean's `StateT S M X` is `S → M (X × S)`: the pairs are `(value, state)`, where
Rocq's `stateT` uses `(state, value)`. The `Proper (equ …)` instances are not needed (`=`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)
open Coinduction

variable {E F C D : Effect.{u}} {S X : Type u}

/-! ## Monad operations lifted to `StateT` -/

section StateMonadOperations
variable {M : Type u → Type u} [Monad M]

instance [MonadBr C M] : MonadBr C (StateT S M) := ⟨fun c s => do let x ← mbr c; pure (x, s)⟩
instance [MonadTrigger E M] : MonadTrigger E (StateT S M) :=
  ⟨fun e s => do let x ← mtrigger e; pure (x, s)⟩
instance [MonadStuck M] : MonadStuck (StateT S M) := ⟨fun _ => mstuck⟩
instance [MonadStep M] : MonadStep (StateT S M) := ⟨fun s => do let _ ← mstep; pure (⟨⟩, s)⟩

variable [ITree.MonadIter M] [MonadStuck M] [MonadStep M]

/-- `foldM` into a state monad. -/
def fold_state (h : (e : E.I) → StateT S M (E.O e)) (g : (c : C.I) → StateT S M (C.O c)) :
    CTree E C X → StateT S M X :=
  foldM h g

/-- `interp` into a state monad. -/
def interp_state [MonadBr C M] (h : (e : E.I) → StateT S M (E.O e)) :
    CTree E C X → StateT S M X :=
  interp h

/-- `refine` into a state monad. -/
def refine_state [MonadTrigger E M] (g : (c : C.I) → StateT S M (C.O c)) :
    CTree E C X → StateT S M X :=
  refine g

end StateMonadOperations

/-! ## Unfolding -/

section Unfold
variable (h : (e : E.I) → StateT S (CTree F D) (E.O e))
  (g : (c : C.I) → StateT S (CTree F D) (C.O c))

/-- The loop body of `fold_state` at `StateT S (CTree F D)`. -/
private def foldStateStep (p : CTree E C X × S) : CTree F D ((CTree E C X × S) ⊕ (X × S)) :=
  match p with
  | (t, s) => (fun (ba, s) => ba.map (·, s) (·, s)) <$> (foldStep h g t).run s

private theorem fold_state_eq_iter (t : CTree E C X) (s : S) :
    fold_state h g t s = CTree.iter (foldStateStep h g) (t, s) := rfl

theorem unfold_fold_state (t : CTree E C X) (s : S) :
    fold_state h g t s = match t.unfold with
      | .ret r => pure (r, s)
      | .stuck => .stuck
      | .guard t => .guard (fold_state h g t s)
      | .step t => .step (.guard (fold_state h g t s))
      | .vis e k => h e s >>= fun xs => .guard (fold_state h g (k xs.1) xs.2)
      | .br c k => g c s >>= fun xs => .guard (fold_state h g (k xs.1) xs.2) := by
  rw [fold_state_eq_iter, unfold_iter]
  cases t <;> simp [foldStateStep, foldStep, StateT.run_map, mstuck, mstep, StateT.run_pure,
    fold_state_eq_iter] <;> simp [StateT.run]


@[simp] theorem fold_state_ret (r : X) (s : S) :
    fold_state h g (pure r : CTree E C X) s = pure (r, s) := by
  rw [unfold_fold_state]; simp
@[simp] theorem fold_state_stuck (s : S) : fold_state h g (.stuck : CTree E C X) s = .stuck := by
  rw [unfold_fold_state]; simp
@[simp] theorem fold_state_guard (t : CTree E C X) (s : S) :
    fold_state h g t.guard s = (fold_state h g t s).guard := by
  rw [unfold_fold_state]; simp
@[simp] theorem fold_state_step (t : CTree E C X) (s : S) :
    fold_state h g t.step s = (fold_state h g t s).guard.step := by
  rw [unfold_fold_state]; simp
@[simp] theorem fold_state_vis (e : E.I) (k : E.O e → CTree E C X) (s : S) :
    fold_state h g (.vis e k) s = h e s >>= fun xs => .guard (fold_state h g (k xs.1) xs.2) := by
  rw [unfold_fold_state]; simp
@[simp] theorem fold_state_br (c : C.I) (k : C.O c → CTree E C X) (s : S) :
    fold_state h g (.br c k) s = g c s >>= fun xs => .guard (fold_state h g (k xs.1) xs.2) := by
  rw [unfold_fold_state]; simp

theorem fold_state_trigger (e : E.I) (s : S) :
    fold_state h g (CTree.trigger e : CTree E C (E.O e)) s = h e s >>= fun x => .guard (pure x) := by
  simp [CTree.trigger]

theorem fold_state_trigger_sb (e : E.I) (s : S) :
    fold_state h g (CTree.trigger e : CTree E C (E.O e)) s ~ h e s := by
  rw [fold_state_trigger]
  conv => rhs; rw [← bind_pure (h e s)]
  exact sbisim_clo_bind_eq (sbisim_refl _) fun x => sb_guard _

theorem interp_state_eq_fold_state [C -< D] :
    (interp_state h : CTree E C X → StateT S (CTree F D) X) = fold_state h mbr := rfl

theorem unfold_interp_state [C -< D] (t : CTree E C X) (s : S) :
    interp_state h t s = match t.unfold with
      | .ret r => pure (r, s)
      | .stuck => .stuck
      | .guard t => .guard (interp_state h t s)
      | .step t => .step (.guard (interp_state h t s))
      | .vis e k => h e s >>= fun xs => .guard (interp_state h (k xs.1) xs.2)
      | .br c k => (mbr c : StateT S (CTree F D) (C.O c)) s >>= fun xs =>
          .guard (interp_state h (k xs.1) xs.2) :=
  unfold_fold_state h mbr t s

section Interp
variable [C -< D]
@[simp] theorem interp_state_ret (r : X) (s : S) :
    interp_state h (pure r : CTree E C X) s = (pure (r, s) : CTree F D (X × S)) :=
  fold_state_ret h mbr r s
@[simp] theorem interp_state_stuck (s : S) :
    interp_state h (.stuck : CTree E C X) s = (.stuck : CTree F D (X × S)) :=
  fold_state_stuck h mbr s
@[simp] theorem interp_state_guard (t : CTree E C X) (s : S) :
    interp_state h t.guard s = (interp_state h t s).guard :=
  fold_state_guard h mbr t s
@[simp] theorem interp_state_step (t : CTree E C X) (s : S) :
    interp_state h t.step s = (interp_state h t s).guard.step :=
  fold_state_step h mbr t s
@[simp] theorem interp_state_vis (e : E.I) (k : E.O e → CTree E C X) (s : S) :
    interp_state h (.vis e k) s = h e s >>= fun xs => .guard (interp_state h (k xs.1) xs.2) :=
  fold_state_vis h mbr e k s
@[simp] theorem interp_state_br (c : C.I) (k : C.O c → CTree E C X) (s : S) :
    interp_state h (.br c k) s =
      (CTree.branch' C c : CTree F D (C.O c)) >>= fun x => .guard (interp_state h (k x) s) := by
  rw [unfold_interp_state]; simp [mbr]

theorem interp_state_trigger (e : E.I) (s : S) :
    interp_state h (CTree.trigger e : CTree E C (E.O e)) s = h e s >>= fun x => .guard (pure x) :=
  fold_state_trigger h mbr e s

theorem interp_interp_state (t : CTree E C X) :
    (interp h t : StateT S (CTree F D) X) = interp_state h t := rfl
end Interp

theorem unfold_refine_state [E -< F] (t : CTree E C X) (s : S) :
    refine_state g t s = match t.unfold with
      | .ret r => pure (r, s)
      | .stuck => .stuck
      | .guard t => .guard (refine_state g t s)
      | .step t => .step (.guard (refine_state g t s))
      | .vis e k => (mtrigger e : CTree F D (E.O e)) >>= fun x => .guard (refine_state g (k x) s)
      | .br c k => g c s >>= fun xs => .guard (refine_state g (k xs.1) xs.2) := by
  show fold_state mtrigger g t s = _
  rw [unfold_fold_state]; cases t <;> simp [mtrigger] <;> rfl

section Refine
variable [E -< F]
@[simp] theorem refine_state_ret (r : X) (s : S) :
    refine_state g (pure r : CTree E C X) s = (pure (r, s) : CTree F D (X × S)) :=
  fold_state_ret mtrigger g r s
@[simp] theorem refine_state_stuck (s : S) :
    refine_state g (.stuck : CTree E C X) s = (.stuck : CTree F D (X × S)) :=
  fold_state_stuck mtrigger g s
@[simp] theorem refine_state_guard (t : CTree E C X) (s : S) :
    refine_state g t.guard s = (refine_state g t s).guard :=
  fold_state_guard mtrigger g t s
@[simp] theorem refine_state_step (t : CTree E C X) (s : S) :
    refine_state g t.step s = (refine_state g t s).guard.step :=
  fold_state_step mtrigger g t s
@[simp] theorem refine_state_vis (e : E.I) (k : E.O e → CTree E C X) (s : S) :
    refine_state g (.vis e k) s =
      (mtrigger e : CTree F D (E.O e)) >>= fun x => .guard (refine_state g (k x) s) := by
  rw [unfold_refine_state]; simp
@[simp] theorem refine_state_br (c : C.I) (k : C.O c → CTree E C X) (s : S) :
    refine_state g (.br c k) s = g c s >>= fun xs => .guard (refine_state g (k xs.1) xs.2) :=
  fold_state_br mtrigger g c k s
end Refine

end Unfold

/-! ## `bind` -/

section FoldBind
variable (h : (e : E.I) → StateT S (CTree F D) (E.O e))
  (g : (c : C.I) → StateT S (CTree F D) (C.O c))

theorem fold_state_bind {A B : Type u} (t : CTree E C A) (k : A → CTree E C B) (s : S) :
    fold_state h g (t >>= k) s =
      fold_state h g t s >>= fun st => fold_state h g (k st.1) st.2 := by
  let Fk : CTree E C A × S → CTree F D (B × S) := fun p => fold_state h g (p.1 >>= k) p.2
  let Gk : CTree E C A × S → CTree F D (B × S) := fun p =>
    fold_state h g p.1 p.2 >>= fun st => fold_state h g (k st.1) st.2
  let R : CTree F D (B × S) → CTree F D (B × S) → Prop := fun a b =>
    (∃ v : CTree F D (CTree E C A × S), a = v >>= (fun p => (Fk p).guard) ∧
      b = v >>= (fun p => (Gk p).guard)) ∨ ∃ p, a = Fk p ∧ b = Gk p
  have c1 : ∀ v : CTree F D (CTree E C A × S),
      EqF (fun a b => R a b ∨ a = b) (v >>= (fun p => (Fk p).guard)).unfold
        (v >>= (fun p => (Gk p).guard)).unfold := by
    intro v
    cases v with
    | ret p => simp only [pure_bind, unfold_guard]; exact .guard (.inl (.inr ⟨p, rfl, rfl⟩))
    | stuck => simp; exact .stuck
    | step v => simp only [step_bind, unfold_step]; exact .step (.inl (.inl ⟨v, rfl, rfl⟩))
    | guard v => simp only [guard_bind, unfold_guard]; exact .guard (.inl (.inl ⟨v, rfl, rfl⟩))
    | vis e kv => simp only [vis_bind, unfold_vis]; exact .vis e fun x => .inl (.inl ⟨kv x, rfl, rfl⟩)
    | br c kv => simp only [br_bind, unfold_br]; exact .br c fun x => .inl (.inl ⟨kv x, rfl, rfl⟩)
  refine eq_coind_upto R ?_ _ _ (.inr ⟨(t, s), rfl, rfl⟩)
  rintro a b (⟨v, rfl, rfl⟩ | ⟨⟨t, s⟩, rfl, rfl⟩)
  · exact c1 v
  · cases t with
    | ret r =>
      simp only [Fk, Gk, pure_bind, fold_state_ret]
      exact EqF.refl (fun _ => Or.inr rfl) _
    | stuck => simp [Fk, Gk]; exact .stuck
    | guard t =>
      simp only [Fk, Gk, guard_bind, fold_state_guard, unfold_guard]
      exact .guard (.inl (.inr ⟨(t, s), rfl, rfl⟩))
    | step t =>
      simp only [Fk, Gk, step_bind, fold_state_step, unfold_step]
      exact .step (.inl (.inl ⟨pure (t, s), by simp [Fk], by simp [Gk]⟩))
    | vis e k' =>
      have := c1 (h e s >>= fun xs => pure (k' xs.1, xs.2))
      simpa [Fk, Gk, bind_assoc] using this
    | br c k' =>
      have := c1 (g c s >>= fun xs => pure (k' xs.1, xs.2))
      simpa [Fk, Gk, bind_assoc] using this

theorem interp_state_bind [C -< D] {A B : Type u} (t : CTree E C A) (k : A → CTree E C B)
    (s : S) :
    interp_state h (t >>= k) s = interp_state h t s >>= fun st => interp_state h (k st.1) st.2 :=
  fold_state_bind h mbr t k s

theorem refine_state_bind [E -< F] {A B : Type u} (t : CTree E C A) (k : A → CTree E C B)
    (s : S) :
    refine_state g (t >>= k) s = refine_state g t s >>= fun st => refine_state g (k st.1) st.2 :=
  fold_state_bind mtrigger g t k s

end FoldBind

/-! ## The state effect -/

section StateE
variable (S : Type u)

/-- Operations of the state effect (Rocq `stateE`'s constructors `Get`, `Put`). -/
inductive StateOp
  | get
  | put (s : S)

/-- The state effect: `get` answers the state, `put s` answers `⟨⟩`. -/
def stateE : Effect.{u} := ⟨StateOp S, fun | .get => S | .put _ => PUnit⟩

variable {S}

/-- Read the state. -/
def get [stateE S -< E] : CTree E C S := CTree.trigger' (stateE S) StateOp.get

/-- Overwrite the state. -/
def put [stateE S -< E] (s : S) : CTree E C PUnit := CTree.trigger' (stateE S) (StateOp.put s)

/-- The standard handler of the state effect. -/
def h_state : (e : (stateE S).I) → StateT S (CTree E C) ((stateE S).O e)
  | .get => fun s => pure (s, s)
  | .put s' => fun _ => pure (⟨⟩, s')

/-- Re-emit an event, leaving the state unchanged. -/
def pure_state (e : E.I) : StateT S (CTree E C) (E.O e) := fun s =>
  CTree.trigger e >>= fun x => pure (x, s)

/-- Re-emit a branching, leaving the state unchanged. -/
def pure_state_choice (c : C.I) : StateT S (CTree E C) (C.O c) := fun s =>
  CTree.branch c >>= fun x => pure (x, s)

/-- Run the state effect of a tree. -/
def run_state : CTree (stateE S ⊕ₑ E) C X → StateT S (CTree E C) X :=
  fold_state (fun | .inl e => h_state e | .inr e => pure_state e) pure_state_choice

end StateE

/-! ## `interp_state`: internal paths and transitions -/

section InterpState
variable {B : Effect.{u}} [B -< C] {St : Type u} (h : (e : E.I) → StateT St (CTree F C) (E.O e))

/-- Rocq instance `epsilon_det_interp_state`. -/
theorem epsilon_det_interp_state {t t' : CTree E B X} (H : EpsilonDet t t') (s : St) :
    EpsilonDet (interp_state h t s) (interp_state h t' s) := by
  induction H with
  | refl => exact .refl _
  | guard _ ih => rw [interp_state_guard]; exact .guard ih

theorem epsilon_interp_state [LawfulSubeffect B C] {t t' : CTree E B X} (H : Epsilon t t')
    (s : St) : Epsilon (interp_state h t s) (interp_state h t' s) := by
  induction H with
  | refl => exact .refl _
  | br x _ ih =>
    rw [interp_state_br, bind_branch', CTree.br']
    obtain ⟨y, hy⟩ := LawfulSubeffect.map_surj (E₂ := C) _ x
    exact .br y (by rw [hy]; exact .guard ih)
  | guard _ ih => rw [interp_state_guard]; exact .guard ih

theorem interp_state_ret_inv (s : St) (t : CTree E B X) (r : X × St)
    (H : interp_state h t s = pure r) : t = pure r.1 ∧ s = r.2 := by
  cases t with
  | ret x => simp at H; subst H; simp
  | vis e k =>
    rw [interp_state_vis] at H
    obtain ⟨_, _, H⟩ := pure_eq_bind_inv H
    simp at H
  | br c k => simp [CTree.br'] at H
  | _ => simp at H

theorem trans_val_interp_state [LawfulSubeffect B C] {t u : CTree E B X} {v : X} (st : St)
    (H : trans (.val v) t u) : trans (.val (v, st)) (interp_state h t st) .stuck := by
  obtain ⟨he, -⟩ := trans_val_epsilon H
  exact epsilon_trans (epsilon_interp_state h he st) (by rw [interp_state_ret]; exact trans_ret _)

theorem trans_τ_interp_state [LawfulSubeffect B C] {t u : CTree E B X} (st : St)
    (H : trans .tau t u) : trans .tau (interp_state h t st) (.guard (interp_state h u st)) := by
  obtain ⟨u', he, rfl⟩ := trans_τ_epsilon H
  exact epsilon_trans (epsilon_interp_state h he st) (by rw [interp_state_step]; exact trans_step _)

/-- Rocq's `u';; Guard …` is `u' >>= fun _ => .guard …`. -/
theorem trans_obs_interp_state_step [LawfulSubeffect B C] {t u : CTree E B X} {e : E.I}
    {x : E.O e} {st st' : St} {u' : CTree F C (E.O e × St)} {l : Label F}
    (H : trans (.obs e x) t u) (Hh : trans l (h e st) u') (hl : ¬ IsVal l)
    (hd : EpsilonDet u' (pure (x, st'))) :
    trans l (interp_state h t st) (u' >>= fun _ => .guard (interp_state h u st')) := by
  obtain ⟨k, he, rfl⟩ := trans_obs_epsilon H
  refine epsilon_trans (epsilon_interp_state h he st) ?_
  rw [interp_state_vis]
  have := trans_bind_l (k := fun sx => .guard (interp_state h (k sx.1) sx.2)) hl Hh
  rwa [epsilon_det_bind_ret_l_equ hd] at this

theorem trans_obs_interp_state_pure [LawfulSubeffect B C] {t u : CTree E B X} {e : E.I}
    {x : E.O e} {st st' : St} (H : trans (.obs e x) t u)
    (Hh : trans (.val (x, st')) (h e st) .stuck) :
    Epsilon (interp_state h t st) (.guard (interp_state h u st')) := by
  obtain ⟨k, he, rfl⟩ := trans_obs_epsilon H
  have e1 := epsilon_interp_state h he st
  rw [interp_state_vis] at e1
  exact e1.trans (epsilon_bind_ret (trans_val_epsilon Hh).1)

end InterpState

/-! ## Lifting a stateless handler -/

/-- Equality coinduction for two families of trees that may continue after an arbitrary prefix
`v`, each continuation under a `guard`. -/
private theorem eq_coind_guard_bind {Y A : Type u} (Fk Gk : A → CTree E C Y)
    (H : ∀ p, (∃ v : CTree E C A, Fk p = v >>= (fun p => (Fk p).guard) ∧
        Gk p = v >>= (fun p => (Gk p).guard)) ∨
      EqF (fun a b => ((∃ v : CTree E C A, a = v >>= (fun p => (Fk p).guard) ∧
        b = v >>= (fun p => (Gk p).guard)) ∨ ∃ p, a = Fk p ∧ b = Gk p) ∨ a = b)
        (Fk p).unfold (Gk p).unfold) :
    ∀ p, Fk p = Gk p := by
  let R : CTree E C Y → CTree E C Y → Prop := fun a b =>
    (∃ v : CTree E C A, a = v >>= (fun p => (Fk p).guard) ∧ b = v >>= (fun p => (Gk p).guard)) ∨
      ∃ p, a = Fk p ∧ b = Gk p
  have c1 : ∀ v : CTree E C A,
      EqF (fun a b => R a b ∨ a = b) (v >>= (fun p => (Fk p).guard)).unfold
        (v >>= (fun p => (Gk p).guard)).unfold := by
    intro v
    cases v with
    | ret p => simp only [pure_bind, unfold_guard]; exact .guard (.inl (.inr ⟨p, rfl, rfl⟩))
    | stuck => simp; exact .stuck
    | step v => simp only [step_bind, unfold_step]; exact .step (.inl (.inl ⟨v, rfl, rfl⟩))
    | guard v => simp only [guard_bind, unfold_guard]; exact .guard (.inl (.inl ⟨v, rfl, rfl⟩))
    | vis e kv => simp only [vis_bind, unfold_vis]; exact .vis e fun x => .inl (.inl ⟨kv x, rfl, rfl⟩)
    | br c kv => simp only [br_bind, unfold_br]; exact .br c fun x => .inl (.inl ⟨kv x, rfl, rfl⟩)
  intro p
  refine eq_coind_upto R ?_ _ _ (Or.inr ⟨p, rfl, rfl⟩)
  rintro a b (⟨v, rfl, rfl⟩ | ⟨p, rfl, rfl⟩)
  · exact c1 v
  · rcases H p with ⟨v, e1, e2⟩ | H
    · rw [e1, e2]; exact c1 v
    · exact H

section LiftHandler
variable (h : (e : E.I) → CTree F C (E.O e))

/-- A stateless handler, as a handler over the trivial state. -/
def lift_handler : (e : E.I) → StateT PUnit (CTree F C) (E.O e) :=
  fun e _ => (fun x => (x, ⟨⟩)) <$> h e

theorem is_simple_lift_handler (H : ∀ e, isSimple (h e)) (e : E.I) (st : PUnit) :
    isSimple (lift_handler h e st) :=
  is_simple_map _ (H e)

/-- Results on `interp_state` transport to `interp`. -/
theorem interp_lift_handler {B : Effect.{u}} [B -< C] (t : CTree E B X) :
    interp h t = (fun p => p.1) <$> interp_state (lift_handler h) t ⟨⟩ := by
  refine eq_coind_guard_bind (fun t => interp h t)
    (fun t => (fun p => p.1) <$> interp_state (lift_handler h) t ⟨⟩) ?_ t
  intro t
  cases t with
  | ret r => exact .inr (by simp; exact .ret _)
  | stuck => exact .inr (by simp; exact .stuck)
  | guard t => exact .inr (by simp; exact .guard (.inl (.inr ⟨t, rfl, rfl⟩)))
  | step t => exact .inr (by simp; exact .step (.inl (.inl ⟨pure t, by simp, by simp⟩)))
  | vis e k => exact .inl ⟨h e >>= fun x => pure (k x), by simp, by simp [lift_handler]⟩
  | br c k =>
    refine .inr ?_
    simp only [interp_br', interp_state_br, bind_branch', CTree.br', map_br, unfold_br, map_guard]
    exact .br _ fun x => .inl (.inl ⟨pure (k ((Subeffect.map c).2 x)), by simp, by simp⟩)

end LiftHandler

/-! ## Simulation of handlers lifts to `interp_state` -/

private theorem stateT_map_apply {σ α β : Type u} (f : α → β) (m : StateT σ (CTree F D) α)
    (s : σ) : (f <$> m) s = (fun p => (f p.1, p.2)) <$> m s := StateT.run_map f m s

theorem ssim_interp_state_h {F₁ F₂ D₁ D₂ : Effect.{u}} [C -< D₁] [C -< D₂] [LawfulSubeffect C D₂]
    {St St' : Type u} (Ldest : Label F₁ → Label F₂ → Prop) (Rs : St → St' → Prop)
    (h : (e : E.I) → StateT St (CTree F₁ D₁) (E.O e))
    (h' : (e : E.I) → StateT St' (CTree F₂ D₂) (E.O e))
    (HL : Ldest .tau .tau ∧ ∀ (x : X) st st', Rs st st' → Ldest (.val (x, st)) (.val (x, st')))
    (Hh : ∀ e st st', Rs st st' → ssim (UpdateValRel Ldest
      (fun (zs : E.O e × St) (zs' : E.O e × St') => Rs zs.2 zs'.2 ∧ zs.1 = zs'.1)) (h e st) (h' e st'))
    (t : CTree E C X) (st₀ : St) (st₀' : St') (hs : Rs st₀ st₀') :
    ssim Ldest (interp_state h t st₀) (interp_state h' t st₀') := by
  let Ra : CTree E C X × St → CTree E C X × St' → Prop := fun p p' => p.1 = p'.1 ∧ Rs p.2 p'.2
  let Rb : X × St → X × St' → Prop := fun b b' => Ldest (.val b) (.val b')
  refine ssim_iter (L0 := UpdateValRel Ldest (sumRel Ra Rb)) Ldest Ra Rb updateValRel_correct
    (fun _ _ => Iff.rfl) (foldStateStep h mbr) (foldStateStep h' mbr) ?_ (t, st₀) (t, st₀') ⟨rfl, hs⟩
  rintro ⟨t, st⟩ ⟨t', st'⟩ ⟨rfl, hs⟩
  cases t with
  | ret r =>
    simp [foldStateStep, foldStep, StateT.run_pure]
    exact ssim_ret _ _ (.val _ _ (HL.2 r st st' hs))
  | stuck =>
    simp [foldStateStep, foldStep, mstuck, StateT.run]
    exact stuck_ssim
  | step t =>
    simp only [foldStateStep, foldStep, unfold_step, StateT.run_map]
    simp [mstep, StateT.run]
    exact step_ssim_step (ssim_ret _ _ (UpdateValRel.val _ _
      (show sumRel Ra Rb (.inl (t, st)) (.inl (t, st')) from ⟨rfl, hs⟩)))
      (UpdateValRel.nonval _ _ isVal_tau isVal_tau HL.1)
  | guard t =>
    simp [foldStateStep, foldStep, StateT.run_pure]
    exact ssim_ret _ _ (UpdateValRel.val _ _
      (show sumRel Ra Rb (.inl (t, st)) (.inl (t, st')) from ⟨rfl, hs⟩))
  | vis e k =>
    simp only [foldStateStep, foldStep, unfold_vis, StateT.run_map, Functor.map_map]
    simp only [← bind_pure_comp]
    refine ssim_clo_bind_gen (fun l l' _ _ => updateValRel_updateValRel _ _ _ l l')
      (Hh e st st' hs) ?_
    rintro ⟨z, s⟩ ⟨z', s'⟩ ⟨h₁, h₂⟩
    cases h₂
    exact ssim_ret _ _ (UpdateValRel.val _ _
      (show sumRel Ra Rb (.inl (k z, s)) (.inl (k z, s')) from ⟨rfl, h₁⟩))
  | br c k =>
    simp [foldStateStep, foldStep, stateT_map_apply, mbr, StateT.run, CTree.branch', CTree.br']
    exact ssim_br fun y => by
      obtain ⟨y', hy⟩ := LawfulSubeffect.map_surj (E₂ := D₂) c ((Subeffect.map c).2 y)
      exact ⟨y', by rw [hy]; exact ssim_ret _ _ (UpdateValRel.val _ _
        (show sumRel Ra Rb (.inl (k _, st)) (.inl (k _, st')) from ⟨rfl, hs⟩))⟩

theorem ssim_interp_h {F₁ F₂ D₁ D₂ : Effect.{u}} [C -< D₁] [C -< D₂] [LawfulSubeffect C D₂]
    (Ldest : Label F₁ → Label F₂ → Prop) (h : (e : E.I) → CTree F₁ D₁ (E.O e))
    (h' : (e : E.I) → CTree F₂ D₂ (E.O e)) (HL : Ldest .tau .tau ∧ ∀ x : X, Ldest (.val x) (.val x))
    (Hh : ∀ e, ssim (UpdateValRel Ldest (@Eq (E.O e))) (h e) (h' e)) (t : CTree E C X) :
    ssim Ldest (interp h t) (interp h' t) := by
  rw [interp_lift_handler h, interp_lift_handler h']
  simp only [← bind_pure_comp]
  refine ssim_clo_bind (R0 := Eq) ?_ (by rintro _ _ rfl; exact ssim_ret _ _ (HL.2 _))
  refine ssim_interp_state_h (UpdateValRel Ldest Eq) Eq _ _
    ⟨.nonval _ _ isVal_tau isVal_tau HL.1, by rintro x _ _ rfl; exact .val _ _ rfl⟩ ?_ t PUnit.unit PUnit.unit rfl
  rintro e st _ rfl
  refine ssim_Lequiv (fun l l' _ _ => (updateValRel_updateValRel _ _ _ l l').symm) ?_
  simp only [lift_handler, ← bind_pure_comp]
  exact ssim_clo_bind_gen (R0 := Eq) (fun l l' _ _ => updateValRel_updateValRel _ _ _ l l') (Hh e)
    (by rintro x _ rfl; exact ssim_ret _ _ (.val _ _ ⟨trivial, rfl⟩))

/-! ## `interp_state` preserves `ssim` and `sbisim` for simple handlers -/

section Preservation
variable {B : Effect.{u}} [B -< C] [LawfulSubeffect B C] {St : Type u}
  (h : (e : E.I) → StateT St (CTree F C) (E.O e))

/-- `h e st` is simple and only returns: `h e st` simulates `pure ⟨⟩`, up to its answers. -/
private theorem ssim_pure_handler {Z : Type u} {L : Label F → Label F → Prop} {t : CTree F C Z}
    (Ht : ∀ l t', trans l t t' → IsVal l) :
    ssim (UpdateValRel L (fun (z : Z) (_ : PUnit) => trans (.val z) t .stuck)) t
      (pure PUnit.unit : CTree F C PUnit) := by
  refine ssim_unfold.2 fun l t' TR => ?_
  obtain ⟨v, rfl⟩ := wfVal_isVal_inv (Ht _ _ TR) (wfVal_trans TR)
  cases trans_val_inv TR
  exact ⟨_, _, trans_ret _, stuck_ssim, .val _ _ TR⟩

/-- Rocq instance `interp_state_ssim`. -/
theorem interp_state_ssim (Hh : ∀ e st, isSimple (h e st)) {R : X → X → Prop}
    {t u : CTree E B X} (SIM : ssim (liftValRel R : Label E → Label E → Prop) t u) (st : St) :
    ssim (liftValRel (fun p q : X × St => R p.1 q.1 ∧ p.2 = q.2) : Label F → Label F → Prop)
      (interp_state h t st) (interp_state h u st) := by
  refine ssim_ssim'.2 ?_
  revert t u SIM st
  coinduction CR hR CH
  intro t u SIM st
  show ss' _ CR (interp_state h t st) (interp_state h u st)
  have hst : CR .stuck .stuck := ss_sst' hR _ _ stuck_ss
  have hguard : ∀ {t' u' : CTree E B X} {s : St}, ssim (liftValRel R) t' u' →
      ss' (liftValRel (fun p q : X × St => R p.1 q.1 ∧ p.2 = q.2) : Label F → Label F → Prop) CR
        (interp_state h t' s).guard (interp_state h u' s).guard :=
    fun H => step_ss'_guard (CH H _)
  cases t with
  | ret x =>
    obtain ⟨l, u', TR, hl⟩ := ssim_ret_l_inv SIM
    obtain ⟨y, rfl, hxy⟩ := hl.val_l
    rw [interp_state_ret]
    exact step_ss'_ret_l (y := (y, st)) hst (.val _ _ ⟨hxy, rfl⟩) (trans_val_interp_state h st TR)
  | stuck => rw [interp_state_stuck]; exact ss'_stuck
  | step t =>
    obtain ⟨l, u', TR, SIM', hl⟩ := ssim_step_l_inv SIM
    obtain ⟨-, rfl⟩ := hl.nonval_l isVal_tau
    rw [interp_state_step]
    exact step_ss'_step_l ⟨.tau, _, trans_τ_interp_state h st TR, b_chain hR _ _ (hguard SIM'),
      .nonval _ _ isVal_tau isVal_tau rfl⟩
  | guard t =>
    rw [interp_state_guard]
    exact step_ss'_guard_l (CH (ssim_guard_l_inv SIM) st)
  | vis e k =>
    rw [interp_state_vis]
    rcases Hh e st with Hp | Hs
    · -- pure handler
      have := ss'_chain_bind_gen updateValRel_correct (Chain.step hR) _ _
        (fun xs => (interp_state h (k xs.1) xs.2).guard) (fun _ => interp_state h u st)
        (ssim_pure_handler Hp) ?_
      · simpa using this
      rintro ⟨x, st'⟩ _ TRh
      obtain ⟨l, u', TR, SIM', hl⟩ := ssim_vis_l_inv x SIM
      obtain ⟨-, rfl⟩ := hl.nonval_l isVal_obs
      exact epsilon_ctx_r_sst' (Chain.step hR) _ _
        ⟨_, trans_obs_interp_state_pure h TR TRh, hguard SIM'⟩
    · -- handler that takes exactly one transition
      refine ss_sst' (Chain.step hR) _ _ fun l t' TR => ?_
      rcases trans_bind_inv TR with ⟨hl, th, TRh, rfl⟩ | ⟨x, TRh, -⟩
      · obtain ⟨⟨x, st'⟩, EPS⟩ := Hs _ _ TRh
        obtain ⟨l', u', TRu, SIM', hl'⟩ := ssim_vis_l_inv x SIM
        obtain ⟨-, rfl⟩ := hl'.nonval_l isVal_obs
        refine ⟨l, _, trans_obs_interp_state_step h TRu TRh hl EPS, ?_, .nonval _ _ hl hl rfl⟩
        rw [epsilon_det_bind_ret_l_equ EPS]
        exact ss'_chain_bind_gen (R0 := Eq) (isUpdateValRel_updateValRel_eq _) (Chain.step hR)
          _ _ _ _ (ssim_refl (fun _ => rfl) th)
          (by rintro _ _ rfl; exact hguard SIM')
      · obtain ⟨r, EPS⟩ := Hs _ _ TRh
        generalize hs : (CTree.stuck : CTree F C (E.O e × St)) = s at EPS
        cases EPS <;> simp at hs
  | br c k =>
    rw [interp_state_br, bind_branch', CTree.br']
    exact step_ss'_br_l fun y => b_chain hR _ _
      (step_ss'_guard_l (CH (ssim_br_l_inv SIM _) st))

private theorem prod_eq_rel {A S' : Type u} :
    (fun p q : A × S' => p.1 = q.1 ∧ p.2 = q.2) = Eq :=
  funext fun _ => funext fun _ => propext Prod.ext_iff.symm

/-- Rocq instance `interp_state_ssim_eq`. -/
theorem interp_state_ssim_eq (Hh : ∀ e st, isSimple (h e st)) {t u : CTree E B X} (SIM : t ≲ u)
    (st : St) : interp_state h t st ≲ interp_state h u st := by
  have := interp_state_ssim h Hh (ssim_Lequiv updateValRel_eq.symm SIM) st
  rw [prod_eq_rel] at this
  exact ssim_Lequiv updateValRel_eq this

/-- Rocq instance `interp_ssim_eq`, through `interp_lift_handler`. -/
theorem interp_ssim_eq (h : (e : E.I) → CTree F C (E.O e)) (Hh : ∀ e, isSimple (h e))
    {t u : CTree E B X} (SIM : t ≲ u) : interp h t ≲ interp h u := by
  rw [interp_lift_handler h t, interp_lift_handler h u]
  exact ssim_clo_bind_eq (interp_state_ssim_eq (lift_handler h)
    (fun e => is_simple_lift_handler h Hh e) SIM PUnit.unit) fun _ => ssim_refl (fun _ => rfl) _

private theorem sbisim_Lequiv {Z : Type u} {L L' : Label F → Label F → Prop} (H : Lequiv Z Z L L')
    {t u : CTree F C Z} : sbisim L t u → sbisim L' t u :=
  gfp_mono (b := sb L) (c := sb L') (fun R t u H' => ⟨ss_Lequiv H R t u H'.1,
    ss_Lequiv (fun l l' hl hl' => H l' l hl' hl) _ u t H'.2⟩) t u

theorem interp_state_sbisim_aux (Hh : ∀ e st, isSimple (h e st)) {R : X → X → Prop}
    (hsym : ∀ x y, R x y → R y x) {t u : CTree E B X} (st : St)
    (SIM : ss (liftValRel R : Label E → Label E → Prop) (sbisim (liftValRel R)) t u) :
    gfp (sb' (liftValRel (fun p q : X × St => R p.1 q.1 ∧ p.2 = q.2) : Label F → Label F → Prop))
      true (interp_state h t st) (interp_state h u st) := by
  have hL : ∀ l l', (liftValRel R : Label E → Label E → Prop) l l' → liftValRel R l' l :=
    fun _ _ H => H.symm (fun _ _ => Eq.symm) hsym
  have hL' : ∀ l l', (liftValRel (fun p q : X × St => R p.1 q.1 ∧ p.2 = q.2) :
      Label F → Label F → Prop) l l' → liftValRel _ l' l :=
    fun _ _ H => H.symm (fun _ _ => Eq.symm) fun _ _ h => ⟨hsym _ _ h.1, h.2.symm⟩
  revert t u st SIM
  coinduction CR hR CH
  intro t u st SIM
  show sb' _ CR true (interp_state h t st) (interp_state h u st)
  -- both sides of the `guard`-continuations, from a bisimilar pair
  have hguard : ∀ {t' u' : CTree E B X} {s : St}, sbisim (liftValRel R) t' u' → ∀ side,
      sb' (liftValRel (fun p q : X × St => R p.1 q.1 ∧ p.2 = q.2) : Label F → Label F → Prop) CR
        side (interp_state h t' s).guard (interp_state h u' s).guard := fun H =>
    (split_st' hL' (.step hR)).2 ⟨step_sb'_guard (CH _ (sbisim_unfold.1 H).1),
      step_sb'_guard (CH _
        (sbisim_unfold.1 (sb_chain_symm hL (gfp_chain _) _ _ H)).1)⟩
  cases t with
  | ret x =>
    obtain ⟨l, u', TR, -, hl⟩ := ss_ret_l_inv SIM
    obtain ⟨y, rfl, hxy⟩ := hl.val_l
    rw [interp_state_ret]
    exact sb'_true_ss'.2 (step_ss'_ret_l (y := (y, st)) (fun s => b_chain hR s _ _ (sb'_stuck s))
      (.val _ _ ⟨hxy, rfl⟩) (trans_val_interp_state h st TR))
  | stuck => rw [interp_state_stuck]; exact sb'_true_stuck
  | step t =>
    obtain ⟨l, u', TR, SIM', hl⟩ := ss_step_l_inv SIM
    obtain ⟨-, rfl⟩ := hl.nonval_l isVal_tau
    rw [interp_state_step]
    exact step_sb'_true_step_l hR ⟨.tau, _, trans_τ_interp_state h st TR,
      fun side => b_chain hR side _ _ (hguard SIM' side), .nonval _ _ isVal_tau isVal_tau rfl⟩
  | guard t =>
    rw [interp_state_guard]
    exact step_sb'_true_guard_l hR (CH st (ss_guard_l_inv SIM))
  | vis e k =>
    rw [interp_state_vis]
    rcases Hh e st with Hp | Hs
    · -- pure handler
      refine pure_bind_ctx3_l_sbisim' (fun x => trans (.val x) (h e st) .stuck) (.step hR) true
        _ _ ⟨rfl, h e st, _, rfl, fun l t' TR => ?_, ?_⟩
      · obtain ⟨v, rfl⟩ := wfVal_isVal_inv (Hp _ _ TR) (wfVal_trans TR)
        cases trans_val_inv TR
        exact ⟨v, rfl, TR⟩
      rintro ⟨x, st'⟩ TRh
      obtain ⟨l, u', TR, SIM', hl⟩ := ss_vis_l_inv x SIM
      obtain ⟨-, rfl⟩ := hl.nonval_l isVal_obs
      exact epsilon_ctx3_r_sbisim' (.step hR) true _ _
        ⟨rfl, _, trans_obs_interp_state_pure h TR TRh, hguard SIM' true⟩
    · -- handler that takes exactly one transition
      refine ss_st'_l (.step hR) true _ _ ⟨rfl, fun l t' TR => ?_⟩
      rcases trans_bind_inv TR with ⟨hl, th, TRh, rfl⟩ | ⟨x, TRh, -⟩
      · obtain ⟨⟨x, st'⟩, EPS⟩ := Hs _ _ TRh
        obtain ⟨l', u', TRu, SIM', hl'⟩ := ss_vis_l_inv x SIM
        obtain ⟨-, rfl⟩ := hl'.nonval_l isVal_obs
        refine ⟨l, _, trans_obs_interp_state_step h TRu TRh hl EPS, fun side => ?_,
          .nonval _ _ hl hl rfl⟩
        rw [epsilon_det_bind_ret_l_equ EPS]
        exact sbt'_clo_bind_gen (R0 := Eq) (isUpdateValRel_updateValRel_eq _) hR
          (refl_sb' (fun _ => rfl) (gfp_chain _) side th) (by rintro _ _ rfl b; exact hguard SIM' b)
      · obtain ⟨r, EPS⟩ := Hs _ _ TRh
        generalize hs : (CTree.stuck : CTree F C (E.O e × St)) = s at EPS
        cases EPS <;> simp at hs
  | br c k =>
    rw [interp_state_br, bind_branch', CTree.br']
    exact step_sb'_true_br_l hR fun y => b_chain hR true _ _
      (step_sb'_true_guard_l hR (CH st (ss_br_l_inv SIM _)))

/-- Rocq instance `interp_state_sbisim`. -/
theorem interp_state_sbisim (Hh : ∀ e st, isSimple (h e st)) {R : X → X → Prop}
    (hsym : ∀ x y, R x y → R y x) {t u : CTree E B X}
    (SIM : sbisim (liftValRel R : Label E → Label E → Prop) t u) (st : St) :
    sbisim (liftValRel (fun p q : X × St => R p.1 q.1 ∧ p.2 = q.2) : Label F → Label F → Prop)
      (interp_state h t st) (interp_state h u st) := by
  have hL : ∀ l l', (liftValRel R : Label E → Label E → Prop) l l' → liftValRel R l' l :=
    fun _ _ H => H.symm (fun _ _ => Eq.symm) hsym
  have hL' : ∀ l l', (liftValRel (fun p q : X × St => R p.1 q.1 ∧ p.2 = q.2) :
      Label F → Label F → Prop) l l' → liftValRel _ l' l :=
    fun _ _ H => H.symm (fun _ _ => Eq.symm) fun _ _ h => ⟨hsym _ _ h.1, h.2.symm⟩
  refine sbisim_sbisim'.2 fun side => ?_
  cases side
  · exact (st'_flip hL' (gfp_chain _)).2 (interp_state_sbisim_aux h Hh hsym st
      (sbisim_unfold.1 (sb_chain_symm hL (gfp_chain _) _ _ SIM)).1)
  · exact interp_state_sbisim_aux h Hh hsym st (sbisim_unfold.1 SIM).1

/-- Rocq instance `interp_state_sbisim_eq`. -/
theorem interp_state_sbisim_eq (Hh : ∀ e st, isSimple (h e st)) {t u : CTree E B X} (SIM : t ~ u)
    (st : St) : interp_state h t st ~ interp_state h u st := by
  have := interp_state_sbisim h Hh (fun _ _ => Eq.symm) (sbisim_Lequiv updateValRel_eq.symm SIM) st
  rw [prod_eq_rel] at this
  exact sbisim_Lequiv updateValRel_eq this

/-- Rocq instance `interp_sbisim_eq`, through `interp_lift_handler`. -/
theorem interp_sbisim_eq (h : (e : E.I) → CTree F C (E.O e)) (Hh : ∀ e, isSimple (h e))
    {t u : CTree E B X} (SIM : t ~ u) : interp h t ~ interp h u := by
  rw [interp_lift_handler h t, interp_lift_handler h u]
  exact sbisim_clo_bind_eq (interp_state_sbisim_eq (lift_handler h)
    (fun e => is_simple_lift_handler h Hh e) SIM PUnit.unit) fun _ => sbisim_refl _

end Preservation

end CTree
