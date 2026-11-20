/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.Epsilon

/-!
# Pure trees

`isPure t`: `t` performs no observable action besides returning, i.e. coinductively only
`ret`/`stuck`/`br`/`guard` nodes. `PureFinite` is its inductive (finite) variant, and `isSimple t`
states that every transition of `t` either returns or leads to `guard*` of a return (← `Misc/Pure.v`).
Rocq's `pure` is renamed `isPure` to avoid `Pure.pure`.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E C : Effect.{u}} {X Y : Type u}

/-- One step of the `isPure` predicate. -/
inductive PureB (rec : CTree E C X → Prop) (t : CTree E C X) : Prop
  | ret (v : X) : t = pure v → PureB rec t
  | stuck : t = .stuck → PureB rec t
  | br (c : C.I) (k : C.O c → CTree E C X) : t = .br c k → (∀ v, rec (k v)) → PureB rec t
  | guard (u : CTree E C X) : t = .guard u → rec u → PureB rec t

def fpure : Mon (Pred (CTree E C X)) where
  body := PureB
  mono h _ := fun
    | .ret v e => .ret v e
    | .stuck e => .stuck e
    | .br c k e hk => .br c k e fun v => h _ (hk v)
    | .guard u e hu => .guard u e (h _ hu)

/-- `t` has no observable behaviour besides returning. -/
def isPure (t : CTree E C X) : Prop := gfp fpure t

section IsPure
variable {t t' : CTree E C X}

theorem isPure_unfold : isPure t ↔ PureB isPure t :=
  ⟨fun h => gfp_pfp (b := fpure) t h, fun h => b_chain (gfp_chain fpure) t h⟩

theorem isPure_ret (r : X) : isPure (pure r : CTree E C X) := isPure_unfold.2 (.ret r rfl)
theorem isPure_stuck : isPure (.stuck : CTree E C X) := isPure_unfold.2 (.stuck rfl)
theorem isPure_br {c : C.I} {k : C.O c → CTree E C X} (h : ∀ x, isPure (k x)) :
    isPure (.br c k) :=
  isPure_unfold.2 (.br c k rfl h)
theorem isPure_guard (h : isPure t) : isPure t.guard := isPure_unfold.2 (.guard t rfl h)

theorem isPure_br_inv {c : C.I} {k : C.O c → CTree E C X} (x : C.O c) (h : isPure (.br c k)) :
    isPure (k x) := by
  rcases isPure_unfold.1 h with ⟨_, e⟩ | e | ⟨c', k', e, hk⟩ | ⟨_, e, _⟩
  · simp at e
  · simp at e
  · obtain ⟨rfl, e⟩ := br_eq_br_iff'.1 e
    cases e
    exact hk x
  · simp at e

theorem isPure_guard_inv (h : isPure t.guard) : isPure t := by
  rcases isPure_unfold.1 h with ⟨_, e⟩ | e | ⟨_, _, e, _⟩ | ⟨_, e, hu⟩ <;> simp at e
  exact e ▸ hu

theorem pure_productive (h : isPure t) (hp : Productive t) : ∃ r, t = pure r := by
  rcases isPure_unfold.1 h with ⟨v, rfl⟩ | ⟨rfl⟩ | ⟨_, _, rfl, _⟩ | ⟨_, rfl, _⟩
  · exact ⟨v, rfl⟩
  · exact absurd hp productive_stuck
  · exact absurd hp (productive_br _ _)
  · exact absurd hp (productive_guard _)

theorem pure_epsilon (h : isPure t) (he : Epsilon t t') : isPure t' := by
  induction he with
  | refl => exact h
  | br x _ ih => exact ih (isPure_br_inv x h)
  | guard _ ih => exact ih (isPure_guard_inv h)

theorem trans_pure_is_val {l : Label E} (h : isPure t) (ht : trans l t t') : IsVal l := by
  unfold trans at ht
  generalize hT : t.unfold = T at ht
  have eq : t = CTree.fold T := by rw [← hT, fold_unfold]
  subst eq
  clear hT
  induction ht with
  | br x _ ih => exact ih (by simpa using isPure_br_inv x (by simpa using h))
  | guard _ ih => exact ih (by simpa using isPure_guard_inv (by simpa using h))
  | step => rcases isPure_unfold.1 h with ⟨_, e⟩ | e | ⟨_, _, e, _⟩ | ⟨_, e, _⟩ <;> simp at e
  | obs => rcases isPure_unfold.1 h with ⟨_, e⟩ | e | ⟨_, _, e, _⟩ | ⟨_, e, _⟩ <;> simp at e
  | val => exact .val _

theorem trans_bind_pure {k : X → CTree E C Y} {u : CTree E C Y} {l : Label E} (h : isPure t)
    (ht : trans l (t >>= k) u) : ∃ v, trans (.val v) t .stuck ∧ trans l (k v) u := by
  rcases trans_bind_inv ht with ⟨hl, _, ht', _⟩ | h'
  · exact absurd (trans_pure_is_val h ht') hl
  · exact h'

theorem isPure_map (f : X → Y) (h : isPure t) : isPure (f <$> t) := by
  suffices H : ∀ t : CTree E C X, isPure t → isPure (f <$> t) from H t h
  coinduction _ _ CIH
  intro t ht
  rcases isPure_unfold.1 ht with ⟨v, rfl⟩ | ⟨rfl⟩ | ⟨c, k, rfl, hk⟩ | ⟨u, rfl, hu⟩
  · exact .ret (f v) (by simp)
  · exact .stuck (by simp)
  · exact .br c _ (by simp) fun v => CIH (k v) (hk v)
  · exact .guard _ (by simp) (CIH u hu)

end IsPure

/-! ## Finite pure trees -/

inductive PureFinite : CTree E C X → Prop
  | ret (v : X) : PureFinite (pure v)
  | stuck : PureFinite .stuck
  | br (c : C.I) (k : C.O c → CTree E C X) : (∀ v, PureFinite (k v)) → PureFinite (.br c k)
  | guard (u : CTree E C X) : PureFinite u → PureFinite (.guard u)

theorem pure_finite_bind {t : CTree E C X} {k : X → CTree E C Y} (h : PureFinite t)
    (hk : ∀ x, PureFinite (k x)) : PureFinite (t >>= k) := by
  induction h with
  | ret v => simpa using hk v
  | stuck => simpa using PureFinite.stuck
  | br c _ _ ih => simpa using PureFinite.br c _ ih
  | guard _ _ ih => simpa using PureFinite.guard _ ih

theorem pure_pure_finite {t : CTree E C X} (h : PureFinite t) : isPure t := by
  induction h with
  | ret v => exact isPure_ret v
  | stuck => exact isPure_stuck
  | br _ _ _ ih => exact isPure_br ih
  | guard _ _ ih => exact isPure_guard ih

theorem isStuck_pure {t : CTree E C X} {k : X → CTree E C Y} (h : isPure t)
    (hk : ∀ x, isStuck (k x)) : isStuck (t >>= k) := fun _ _ ht =>
  let ⟨x, _, h'⟩ := trans_bind_pure h ht
  hk x _ _ h'

/-! ## Simple trees -/

/-- Every transition of `t` either returns, or leads to `guard*` of a return. -/
def isSimple (t : CTree E C X) : Prop :=
  (∀ l t', trans l t t' → IsVal l) ∨ (∀ l t', trans l t t' → ∃ r, EpsilonDet t' (pure r))

section IsSimple

theorem is_simple_ret (r : X) : isSimple (pure r : CTree E C X) :=
  .inl fun _ _ h => (trans_ret_inv h).2 ▸ .val r

theorem is_simple_guard_ret (r : X) : isSimple (CTree.guard (pure r) : CTree E C X) :=
  .inl fun _ _ h => (trans_ret_inv (trans_guard_inv h)).2 ▸ .val r

theorem is_simple_br (c : C.I) : isSimple (CTree.branch c : CTree E C (C.O c)) :=
  .inl fun _ _ h =>
    let ⟨x, h⟩ := trans_br_inv h
    (trans_ret_inv h).2 ▸ .val x

theorem is_simple_map {t : CTree E C X} (f : X → Y) (h : isSimple t) : isSimple (f <$> t) := by
  rw [← bind_pure_comp]
  rcases h with h | h
  · refine .inl fun l t' ht => ?_
    rcases trans_bind_inv ht with ⟨hl, _, ht', _⟩ | ⟨_, _, ht'⟩
    · exact absurd (h _ _ ht') hl
    · exact (trans_ret_inv ht').2 ▸ .val _
  · refine .inr fun l t' ht => ?_
    rcases trans_bind_inv ht with ⟨_, _, ht', rfl⟩ | ⟨_, ht', _⟩
    · obtain ⟨r, hr⟩ := h _ _ ht'
      exact ⟨f r, epsilon_det_bind_ret_l hr (.refl _)⟩
    · obtain ⟨r, hr⟩ := h _ _ ht'
      generalize hs : (CTree.stuck : CTree E C X) = s at hr
      cases hr <;> simp at hs

theorem is_simple_liftState {St : Type u} {t : CTree E C X} (s : St) (h : isSimple t) :
    isSimple (StateT.lift t s : CTree E C (X × St)) := by
  have : (StateT.lift t s : CTree E C (X × St)) = (fun a => (a, s)) <$> t := by
    simp [StateT.lift, bind_pure_comp]
  rw [this]; exact is_simple_map _ h

theorem is_simple_trigger (e : E.I) : isSimple (CTree.trigger e : CTree E C (E.O e)) :=
  .inr fun _ _ h =>
    let ⟨x, h, _⟩ := trans_vis_inv h
    ⟨x, h ▸ .refl _⟩

theorem is_simple_br_inv {c : C.I} {k : C.O c → CTree E C Y} (x : C.O c) (h : isSimple (.br c k)) :
    isSimple (k x) := by
  rcases h with h | h
  · exact .inl fun _ _ ht => h _ _ (trans_br x ht)
  · exact .inr fun _ _ ht => h _ _ (trans_br x ht)

theorem is_simple_pure {t : CTree E C X} (h : isPure t) : isSimple t :=
  .inl fun _ _ ht => trans_pure_is_val h ht

end IsSimple

end CTree
