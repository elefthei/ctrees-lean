/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.Equ

/-!
# The labelled transition system of choice trees

A tree is *observable* if it is a visible event, a return node, or a `step`. `trans l t u`
descends finitely through unobservable `br`/`guard` nodes until it reaches an observable node,
then steps:
- `ret v` steps to `stuck`, emitting `val v`;
- `vis e k` steps to any `k x`, emitting `obs e x`;
- `step t` steps to `t`, emitting `tau`.

`wtrans` (a sequence of `tau` steps, an `etrans` step, and a sequence of `tau` steps) is the
transition relation of weak bisimulation (← `Eq/Trans.v`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)

/-- Labels of the LTS. `val` labels are not statically typed by the return type: typing them makes
lemmas about `bind` awkward to state. -/
inductive Label (E : Effect.{u}) : Type (u + 1)
  | tau
  | obs (e : E.I) (v : E.O e)
  | val {X : Type u} (v : X)

variable {E B : Effect.{u}} {R X Y : Type u}

inductive IsVal : Label E → Prop
  | val {X : Type u} (x : X) : IsVal (.val x)

theorem isVal_tau : ¬ IsVal (.tau : Label E) := nofun
theorem isVal_obs {e : E.I} {v : E.O e} : ¬ IsVal (.obs e v) := nofun

theorem val_eq_invT {x : X} {y : Y} (h : (Label.val x : Label E) = .val y) : X = Y := by
  cases h; rfl
theorem val_eq_inv {x y : X} (h : (Label.val x : Label E) = .val y) : x = y := by
  cases h; rfl
theorem obs_eq_inv {e₁ e₂ : E.I} {v₁ : E.O e₁} {v₂ : E.O e₂} (h : Label.obs e₁ v₁ = .obs e₂ v₂) :
    e₁ = e₂ ∧ HEq v₁ v₂ := by
  cases h; exact ⟨rfl, .rfl⟩

/-- The transition relation, on an unfolded source. -/
inductive Trans_ : Label E → CTreeF E B R (CTree E B R) → CTree E B R → Prop
  | br {c : B.I} (x : B.O c) {k : B.O c → CTree E B R} {l t} :
      Trans_ l (k x).unfold t → Trans_ l (.br c k) t
  | guard {t t' : CTree E B R} {l} : Trans_ l t.unfold t' → Trans_ l (.guard t) t'
  | step {t : CTree E B R} : Trans_ .tau (.step t) t
  | obs {e : E.I} {k : E.O e → CTree E B R} (x : E.O e) : Trans_ (.obs e x) (.vis e k) (k x)
  | val {r : R} : Trans_ (.val r) (.ret r) .stuck

/-- The transition relation over `CTree`s. -/
def trans (l : Label E) (t u : CTree E B R) : Prop := Trans_ l t.unfold u

/-- `trans` extended with its reflexive closure, labelled by `tau`. -/
def etrans (l : Label E) (t u : CTree E B R) : Prop :=
  match l with
  | .tau => trans .tau t u ∨ t = u
  | _ => trans l t u

/-- One or more `tau` steps. -/
def τtrans : CTree E B R → CTree E B R → Prop := Relation.TransGen (trans .tau)

/-- Weak transition: `(trans tau)^* ⋅ etrans l ⋅ (trans tau)^*`. -/
def wtrans (l : Label E) (t u : CTree E B R) : Prop :=
  ∃ t₁ t₂, Star (trans .tau) t t₁ ∧ etrans l t₁ t₂ ∧ Star (trans .tau) t₂ u

/-- Proper weak transition: `(trans tau)^* ⋅ trans l ⋅ (trans tau)^*`. -/
def pwtrans (l : Label E) (t u : CTree E B R) : Prop :=
  ∃ t₁ t₂, Star (trans .tau) t t₁ ∧ trans l t₁ t₂ ∧ Star (trans .tau) t₂ u

/-- A tree is stuck if it cannot step. -/
def isStuck (t : CTree E B R) : Prop := ∀ l u, ¬ trans l t u

/-- Label relations that relate values to values only. -/
class RespectsVal {E F : Effect.{u}} (L : Label E → Label F → Prop) : Prop where
  respects_val : ∀ l l', L l l' → (IsVal l ↔ IsVal l')

/-- Label relations that relate `tau` to `tau` only. -/
class RespectsTau {E F : Effect.{u}} (L : Label E → Label F → Prop) : Prop where
  respects_tau : ∀ l l', L l l' → (l = .tau ↔ l' = .tau)

/-- Label relations that relate observations only when they are equal. -/
def eqObs (L : Label E → Label E → Prop) : Prop :=
  ∀ (e e' : E.I) (x : E.O e) (x' : E.O e'), L (.obs e x) (.obs e' x') → Label.obs e x = .obs e' x'

instance : RespectsVal (@Eq (Label E)) := ⟨by rintro _ _ rfl; rfl⟩
instance : RespectsTau (@Eq (Label E)) := ⟨by rintro _ _ rfl; rfl⟩

/-! ## Elementary theory of the transition relations -/

section Elementary
variable {l : Label E} {t u v : CTree E B R}

theorem etrans_iff : etrans l t u ↔ trans l t u ∨ (l = .tau ∧ t = u) := by
  cases l <;> simp [etrans]

theorem trans_etrans (h : trans l t u) : etrans l t u := etrans_iff.2 (.inl h)
theorem etrans_wtrans (h : etrans l t u) : wtrans l t u := ⟨t, u, .refl, h, .refl⟩
theorem trans_wtrans (h : trans l t u) : wtrans l t u := etrans_wtrans (trans_etrans h)
theorem pwtrans_wtrans (h : pwtrans l t u) : wtrans l t u :=
  let ⟨t₁, t₂, h₁, h₂, h₃⟩ := h; ⟨t₁, t₂, h₁, trans_etrans h₂, h₃⟩

theorem enil : etrans .tau t t := Or.inr rfl
theorem wnil : wtrans .tau t t := etrans_wtrans enil

theorem wtrans_τ : wtrans .tau t u ↔ Star (trans .tau) t u := by
  constructor
  · rintro ⟨t₁, t₂, h₁, h₂ | rfl, h₃⟩
    · exact h₁.trans (Star.head h₂ h₃)
    · exact h₁.trans h₃
  · intro h; exact ⟨t, t, .refl, enil, h⟩

theorem τtrans_wtrans (h : τtrans t u) : wtrans .tau t u := wtrans_τ.2 (Star.of_transGen h)

theorem pwtrans_τ : pwtrans .tau t u ↔ τtrans t u := by
  constructor
  · rintro ⟨t₁, t₂, h₁, h₂, h₃⟩
    exact Star.trans_transGen h₁ (Star.transGen_trans (.single h₂) h₃)
  · intro h
    obtain ⟨w, hw, hwu⟩ : ∃ w, Star (trans .tau) t w ∧ trans .tau w u := by
      induction h with
      | single h => exact ⟨t, .refl, h⟩
      | tail h hbc _ => exact ⟨_, Star.of_transGen h, hbc⟩
    exact ⟨w, u, hw, hwu, .refl⟩

theorem wcons (h₁ : trans .tau t u) (h₂ : wtrans l u v) : wtrans l t v :=
  let ⟨t₁, t₂, h₃, h₄, h₅⟩ := h₂; ⟨t₁, t₂, Star.head h₁ h₃, h₄, h₅⟩

theorem wsnoc (h₁ : wtrans l t u) (h₂ : trans .tau u v) : wtrans l t v :=
  let ⟨t₁, t₂, h₃, h₄, h₅⟩ := h₁; ⟨t₁, t₂, h₃, h₄, h₅.tail h₂⟩

theorem wconss (h₁ : wtrans .tau t u) (h₂ : wtrans l u v) : wtrans l t v :=
  let ⟨t₁, t₂, h₃, h₄, h₅⟩ := h₂; ⟨t₁, t₂, (wtrans_τ.1 h₁).trans h₃, h₄, h₅⟩

theorem wsnocs (h₁ : wtrans l t u) (h₂ : wtrans .tau u v) : wtrans l t v :=
  let ⟨t₁, t₂, h₃, h₄, h₅⟩ := h₁; ⟨t₁, t₂, h₃, h₄, h₅.trans (wtrans_τ.1 h₂)⟩

theorem wtrans_τ_trans (h₁ : wtrans .tau t u) (h₂ : wtrans .tau u v) : wtrans .tau t v :=
  wconss h₁ h₂

end Elementary

/-! ## Backward reasoning for `trans` -/

section Backward
variable {l : Label E}

theorem trans_ret (x : X) : trans (.val x) (pure x : CTree E B X) .stuck := by
  show Trans_ _ (pure x : CTree E B X).unfold _
  rw [unfold_pure]; exact .val

theorem trans_vis {e : E.I} (x : E.O e) (k : E.O e → CTree E B X) :
    trans (.obs e x) (.vis e k) (k x) := by
  show Trans_ _ (CTree.vis e k).unfold _
  rw [unfold_vis]; exact .obs x

theorem trans_br {c : B.I} {k : B.O c → CTree E B X} {t' : CTree E B X} (x : B.O c)
    (h : trans l (k x) t') : trans l (.br c k) t' := by
  show Trans_ _ (CTree.br c k).unfold _
  rw [unfold_br]; exact .br x h

theorem trans_step (t : CTree E B X) : trans .tau (.step t) t := by
  show Trans_ _ t.step.unfold _
  rw [unfold_step]; exact .step

theorem trans_guard {t t' : CTree E B X} (h : trans l t t') : trans l (.guard t) t' := by
  show Trans_ _ t.guard.unfold _
  rw [unfold_guard]; exact .guard h

theorem trans_brS {c : B.I} (k : B.O c → CTree E B X) (x : B.O c) :
    trans .tau (.brS c k) (k x) :=
  trans_br x (trans_step _)

theorem trans_br' {B₁ : Effect.{u}} [B₁ -< B] [LawfulSubeffect B₁ B] {c : B₁.I}
    {k : B₁.O c → CTree E B X} {t' : CTree E B X} (x : B₁.O c) (h : trans l (k x) t') :
    trans l (.br' c k) t' := by
  obtain ⟨y, hy⟩ := LawfulSubeffect.map_surj (E₂ := B) c x
  exact trans_br y (by simpa [hy] using h)

theorem trans_brS' {B₁ : Effect.{u}} [B₁ -< B] [LawfulSubeffect B₁ B] {c : B₁.I}
    (k : B₁.O c → CTree E B X) (x : B₁.O c) : trans .tau (.brS' c k) (k x) :=
  trans_br' x (trans_step _)

theorem trans_vis' {E₁ : Effect.{u}} [E₁ -< E] {e : E₁.I} (k : E₁.O e → CTree E B X)
    (y : E.O (Subeffect.map e).1) :
    trans (.obs (Subeffect.map e).1 y) (.vis' e k) (k ((Subeffect.map e).2 y)) :=
  trans_vis y _

end Backward

/-! ### Bounded branching -/

section BackwardBounded
variable {l : Label E} {t t' u u' v v' w w' : CTree E B X}

section
variable [B2 -< B] [LawfulSubeffect B2 B]
theorem trans_brS2_l : trans .tau (CTree.brS2 t u) t := trans_brS' (B₁ := B2) _ (.up true)
theorem trans_brS2_r : trans .tau (CTree.brS2 t u) u := trans_brS' (B₁ := B2) _ (.up false)
theorem trans_br2_l (h : trans l t t') : trans l (CTree.br2 t u) t' :=
  trans_br' (B₁ := B2) (.up true) h
theorem trans_br2_r (h : trans l u u') : trans l (CTree.br2 t u) u' :=
  trans_br' (B₁ := B2) (.up false) h
end

section
variable [B3 -< B] [LawfulSubeffect B3 B]
theorem trans_brS3_1 : trans .tau (CTree.brS3 t u v) t := trans_brS' (B₁ := B3) _ (.up 0)
theorem trans_brS3_2 : trans .tau (CTree.brS3 t u v) u := trans_brS' (B₁ := B3) _ (.up 1)
theorem trans_brS3_3 : trans .tau (CTree.brS3 t u v) v := trans_brS' (B₁ := B3) _ (.up 2)
theorem trans_br3_1 (h : trans l t t') : trans l (CTree.br3 t u v) t' :=
  trans_br' (B₁ := B3) (.up 0) h
theorem trans_br3_2 (h : trans l u u') : trans l (CTree.br3 t u v) u' :=
  trans_br' (B₁ := B3) (.up 1) h
theorem trans_br3_3 (h : trans l v v') : trans l (CTree.br3 t u v) v' :=
  trans_br' (B₁ := B3) (.up 2) h
end

section
variable [B4 -< B] [LawfulSubeffect B4 B]
theorem trans_brS4_1 : trans .tau (CTree.brS4 t u v w) t := trans_brS' (B₁ := B4) _ (.up 0)
theorem trans_brS4_2 : trans .tau (CTree.brS4 t u v w) u := trans_brS' (B₁ := B4) _ (.up 1)
theorem trans_brS4_3 : trans .tau (CTree.brS4 t u v w) v := trans_brS' (B₁ := B4) _ (.up 2)
theorem trans_brS4_4 : trans .tau (CTree.brS4 t u v w) w := trans_brS' (B₁ := B4) _ (.up 3)
theorem trans_br4_1 (h : trans l t t') : trans l (CTree.br4 t u v w) t' :=
  trans_br' (B₁ := B4) (.up 0) h
theorem trans_br4_2 (h : trans l u u') : trans l (CTree.br4 t u v w) u' :=
  trans_br' (B₁ := B4) (.up 1) h
theorem trans_br4_3 (h : trans l v v') : trans l (CTree.br4 t u v w) v' :=
  trans_br' (B₁ := B4) (.up 2) h
theorem trans_br4_4 (h : trans l w w') : trans l (CTree.br4 t u v w) w' :=
  trans_br' (B₁ := B4) (.up 3) h
end

end BackwardBounded

/-! ## Forward reasoning for `trans` -/

section Forward
variable {l : Label E} {t u : CTree E B X}

theorem trans_ret_inv {x : X} (h : trans l (pure x : CTree E B X) t) : t = .stuck ∧ l = .val x := by
  unfold trans at h; rw [unfold_pure] at h
  cases h; exact ⟨rfl, rfl⟩

theorem trans_vis_inv {e : E.I} {k : E.O e → CTree E B X} (h : trans l (.vis e k) u) :
    ∃ x, u = k x ∧ l = .obs e x := by
  unfold trans at h; rw [unfold_vis] at h
  cases h with | obs x => exact ⟨x, rfl, rfl⟩

theorem trans_br_inv {c : B.I} {k : B.O c → CTree E B X} (h : trans l (.br c k) u) :
    ∃ n, trans l (k n) u := by
  unfold trans at h; rw [unfold_br] at h
  cases h with | br x h => exact ⟨x, h⟩

theorem trans_guard_inv (h : trans l (.guard t) u) : trans l t u := by
  unfold trans at h; rw [unfold_guard] at h
  cases h with | guard h => exact h

theorem trans_step_inv (h : trans l (.step t) u) : u = t ∧ l = .tau := by
  unfold trans at h; rw [unfold_step] at h
  cases h; exact ⟨rfl, rfl⟩

theorem trans_brS_inv {c : B.I} {k : B.O c → CTree E B X} (h : trans l (.brS c k) u) :
    ∃ n, u = k n ∧ l = .tau :=
  let ⟨n, h⟩ := trans_br_inv h; ⟨n, trans_step_inv h⟩

theorem trans_stuck_inv (h : trans l (.stuck : CTree E B X) u) : False := by
  unfold trans at h; rw [unfold_stuck] at h
  cases h

theorem trans_br'_inv {B₁ : Effect.{u}} [B₁ -< B] {c : B₁.I} {k : B₁.O c → CTree E B X}
    (h : trans l (.br' c k) u) : ∃ n, trans l (k n) u :=
  let ⟨_, h⟩ := trans_br_inv h; ⟨_, h⟩

theorem trans_brS'_inv {B₁ : Effect.{u}} [B₁ -< B] {c : B₁.I} {k : B₁.O c → CTree E B X}
    (h : trans l (.brS' c k) u) : ∃ n, u = k n ∧ l = .tau :=
  let ⟨n, h⟩ := trans_br'_inv h; ⟨n, trans_step_inv h⟩

theorem trans_vis'_inv {E₁ : Effect.{u}} [E₁ -< E] {e : E₁.I} {k : E₁.O e → CTree E B X}
    (h : trans l (.vis' e k) u) :
    ∃ y, u = k ((Subeffect.map e).2 y) ∧ l = .obs (Subeffect.map e).1 y :=
  trans_vis_inv h

section Bounded
variable {t t' u v w : CTree E B X}

theorem trans_br2_inv [B2 -< B] (h : trans l (CTree.br2 t u) t') : trans l t t' ∨ trans l u t' := by
  obtain ⟨⟨_ | _⟩, h⟩ := trans_br'_inv h
  · exact .inr h
  · exact .inl h

theorem trans_br3_inv [B3 -< B] (h : trans l (CTree.br3 t u v) t') :
    trans l t t' ∨ trans l u t' ∨ trans l v t' := by
  obtain ⟨⟨⟨_ | _ | _ | _, _⟩⟩, h⟩ := trans_br'_inv h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · omega

theorem trans_br4_inv [B4 -< B] (h : trans l (CTree.br4 t u v w) t') :
    trans l t t' ∨ trans l u t' ∨ trans l v t' ∨ trans l w t' := by
  obtain ⟨⟨⟨_ | _ | _ | _ | _, _⟩⟩, h⟩ := trans_br'_inv h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))
  · omega

theorem trans_brS2_inv [B2 -< B] (h : trans l (CTree.brS2 t u) t') :
    l = .tau ∧ (t' = t ∨ t' = u) := by
  obtain ⟨⟨_ | _⟩, rfl, rfl⟩ := trans_brS'_inv h
  · exact ⟨rfl, .inr rfl⟩
  · exact ⟨rfl, .inl rfl⟩

theorem trans_brS3_inv [B3 -< B] (h : trans l (CTree.brS3 t u v) t') :
    l = .tau ∧ (t' = t ∨ t' = u ∨ t' = v) := by
  obtain ⟨⟨⟨_ | _ | _ | _, _⟩⟩, rfl, rfl⟩ := trans_brS'_inv h
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inr (.inl rfl)⟩
  · exact ⟨rfl, .inr (.inr rfl)⟩
  · omega

theorem trans_brS4_inv [B4 -< B] (h : trans l (CTree.brS4 t u v w) t') :
    l = .tau ∧ (t' = t ∨ t' = u ∨ t' = v ∨ t' = w) := by
  obtain ⟨⟨⟨_ | _ | _ | _ | _, _⟩⟩, rfl, rfl⟩ := trans_brS'_inv h
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inr (.inl rfl)⟩
  · exact ⟨rfl, .inr (.inr (.inl rfl))⟩
  · exact ⟨rfl, .inr (.inr (.inr rfl))⟩
  · omega

end Bounded

/-! Inversion rules based on the label -/

theorem trans__val_inv {x : Y} {T : CTreeF E B X (CTree E B X)} {U : CTree E B X}
    (h : Trans_ (.val x) T U) : U = .stuck := by
  generalize hl : Label.val x = l at h
  induction h with
  | br _ _ ih => exact ih hl
  | guard _ ih => exact ih hl
  | step => cases hl
  | obs => cases hl
  | val => rfl

theorem trans_val_inv {x : Y} (h : trans (.val x) t u) : u = .stuck := trans__val_inv h

theorem trans_val_invT {x : Y} (h : trans (.val x) t u) : X = Y := by
  unfold trans at h
  generalize t.unfold = T at h
  generalize hl : Label.val x = l at h
  induction h with
  | br _ _ ih => exact ih hl
  | guard _ ih => exact ih hl
  | step => cases hl
  | obs => cases hl
  | val => exact (val_eq_invT hl).symm

theorem wtrans_val_inv {x : X} (h : wtrans (.val x) u .stuck) :
    ∃ t, wtrans .tau u t ∧ trans (.val x) t .stuck := by
  obtain ⟨t₁, t₂, h₁, h₂, -⟩ := h
  exact ⟨t₁, wtrans_τ.2 h₁, trans_val_inv h₂ ▸ h₂⟩

end Forward

/-! ## `etrans` theory -/

theorem etrans_case {l : Label E} {t u : CTree E B X} (h : etrans l t u) :
    trans l t u ∨ (l = .tau ∧ t = u) :=
  etrans_iff.1 h

theorem etrans_ret_inv {x : X} {l : Label E} {t : CTree E B X} (h : etrans l (pure x) t) :
    (l = .tau ∧ t = pure x) ∨ (l = .val x ∧ t = .stuck) := by
  rcases etrans_case h with h | ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := trans_ret_inv h; exact .inr ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩

/-! ## Stuck processes -/

section Stuck
variable {l : Label E} {t u : CTree E B X}

theorem etrans_isStuck_inv (hs : isStuck t) (h : etrans l t u) : l = .tau ∧ t = u := by
  rcases etrans_case h with h | h
  · exact (hs _ _ h).elim
  · exact h

theorem transs_isStuck_inv (hs : isStuck t) (h : Star (trans .tau) t u) : t = u := by
  rcases h.cases_head with h | ⟨_, h, _⟩
  · exact h
  · exact (hs _ _ h).elim

theorem wtrans_isStuck_inv (hs : isStuck t) (h : wtrans l t u) : l = .tau ∧ t = u := by
  obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := h
  cases transs_isStuck_inv hs h₁
  obtain ⟨rfl, rfl⟩ := etrans_isStuck_inv hs h₂
  exact ⟨rfl, transs_isStuck_inv hs h₃⟩

theorem stuck_isStuck : isStuck (.stuck : CTree E B X) := fun _ _ h => trans_stuck_inv h

theorem br_empty_isStuck {c : B.I} (k : B.O c → CTree E B X) (hc : B.O c → False) :
    isStuck (.br c k) :=
  fun _ _ h => let ⟨n, _⟩ := trans_br_inv h; hc n

theorem spin_gen_isStuck (c : B.I) : isStuck (CTree.spin_gen c : CTree E B X) := by
  intro l u h
  unfold trans at h
  generalize ht : (CTree.spin_gen c : CTree E B X).unfold = T at h
  induction h with
  | br x _ ih => rw [spin_gen_unfold] at ht; cases ht; exact ih rfl
  | _ => rw [spin_gen_unfold] at ht; cases ht

theorem spin_isStuck : isStuck (CTree.spin : CTree E B X) := by
  intro l u h
  unfold trans at h
  generalize ht : (CTree.spin : CTree E B X).unfold = T at h
  induction h with
  | guard _ ih => rw [spin_unfold] at ht; cases ht; exact ih rfl
  | _ => rw [spin_unfold] at ht; cases ht

theorem spinS_not_isStuck : ¬ isStuck (CTree.spinS : CTree E B X) := fun h =>
  h .tau .spinS (by unfold trans; rw [spinS_unfold]; exact .step)

end Stuck

/-! ## `wtrans` theory -/

section WTrans
variable {l : Label E} {t u : CTree E B X}

theorem wtrans_step (h : wtrans l t u) : wtrans l (.step t) u := wcons (trans_step _) h

theorem trans_τ_str_ret_inv {x : X} (h : Star (trans .tau) (pure x : CTree E B X) t) :
    t = pure x := by
  rcases h.cases_head with h | ⟨_, h, _⟩
  · exact h.symm
  · cases (trans_ret_inv h).2

theorem wtrans_ret_inv {x : X} (h : wtrans l (pure x) t) :
    (l = .tau ∧ t = pure x) ∨ (l = .val x ∧ t = .stuck) := by
  obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := h
  cases trans_τ_str_ret_inv h₁
  rcases etrans_ret_inv h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, trans_τ_str_ret_inv h₃⟩
  · exact .inr ⟨rfl, (transs_isStuck_inv stuck_isStuck h₃).symm⟩

theorem wtrans_val_inv' {x : X} {v : CTree E B X} (h : wtrans (.val x) t v) :
    ∃ u, wtrans .tau t u ∧ trans (.val x) u v ∧ v = .stuck := by
  obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := h
  have h₂' : trans (.val x) t₁ t₂ := h₂
  cases trans_val_inv h₂'
  cases transs_isStuck_inv stuck_isStuck h₃
  exact ⟨t₁, wtrans_τ.2 h₁, h₂', rfl⟩

end WTrans

/-! ## `trans` and `bind` -/

section Bind
variable {l : Label E} {t : CTree E B X} {k : X → CTree E B Y} {u : CTree E B Y}

theorem trans_bind_inv (h : trans l (t >>= k) u) :
    (¬ IsVal l ∧ ∃ t', trans l t t' ∧ u = t' >>= k) ∨
      (∃ x, trans (.val x) t .stuck ∧ trans l (k x) u) := by
  unfold trans at h
  generalize ht : (t >>= k).unfold = T at h
  induction h generalizing t with
  | @br c x k' l u h ih =>
    cases t with
    | ret r =>
      refine .inr ⟨r, trans_ret r, ?_⟩
      simp only [pure_bind] at ht; unfold trans; rw [ht]; exact .br x h
    | br c₀ k₀ =>
      simp only [br_bind, unfold_br] at ht; cases ht
      rcases ih (t := k₀ x) rfl with ⟨hl, t', h₁, rfl⟩ | ⟨y, h₁, h₂⟩
      · exact .inl ⟨hl, t', trans_br x h₁, rfl⟩
      · exact .inr ⟨y, trans_br x h₁, h₂⟩
    | _ => simp at ht
  | @guard t₁ t' l h ih =>
    cases t with
    | ret r =>
      refine .inr ⟨r, trans_ret r, ?_⟩
      simp only [pure_bind] at ht; unfold trans; rw [ht]; exact .guard h
    | guard t₀ =>
      simp only [guard_bind, unfold_guard] at ht; cases ht
      rcases ih (t := t₀) rfl with ⟨hl, t', h₁, rfl⟩ | ⟨y, h₁, h₂⟩
      · exact .inl ⟨hl, t', trans_guard h₁, rfl⟩
      · exact .inr ⟨y, trans_guard h₁, h₂⟩
    | _ => simp at ht
  | @step t₁ =>
    cases t with
    | ret r =>
      refine .inr ⟨r, trans_ret r, ?_⟩
      simp only [pure_bind] at ht; unfold trans; rw [ht]; exact .step
    | step t₀ =>
      simp only [step_bind, unfold_step] at ht; cases ht
      exact .inl ⟨isVal_tau, t₀, trans_step _, rfl⟩
    | _ => simp at ht
  | @obs e k' x =>
    cases t with
    | ret r =>
      refine .inr ⟨r, trans_ret r, ?_⟩
      simp only [pure_bind] at ht; unfold trans; rw [ht]; exact .obs x
    | vis e₀ k₀ =>
      simp only [vis_bind, unfold_vis] at ht; cases ht
      exact .inl ⟨isVal_obs, k₀ x, trans_vis x _, rfl⟩
    | _ => simp at ht
  | @val r =>
    cases t with
    | ret r₀ =>
      refine .inr ⟨r₀, trans_ret r₀, ?_⟩
      simp only [pure_bind] at ht; unfold trans; rw [ht]; exact .val
    | _ => simp at ht

theorem trans_bind_inv_l (h : trans l (t >>= k) u) : ∃ l' t', trans l' t t' := by
  rcases trans_bind_inv h with ⟨_, t', h, _⟩ | ⟨x, h, _⟩
  · exact ⟨_, _, h⟩
  · exact ⟨_, _, h⟩

theorem trans_bind_l {u : CTree E B X} (hl : ¬ IsVal l) (h : trans l t u) :
    trans l (t >>= k) (u >>= k) := by
  unfold trans at *
  rw [← fold_unfold t]
  generalize t.unfold = T at h
  induction h with
  | br x _ ih => simp only [fold_unfold] at ih; simpa using Trans_.br x (ih hl)
  | guard _ ih => simp only [fold_unfold] at ih; simpa using Trans_.guard (ih hl)
  | step => simpa using Trans_.step
  | obs x => simpa using Trans_.obs x
  | val => exact absurd (IsVal.val _) hl

theorem trans_bind_r {x : X} (h₁ : trans (.val x) t .stuck) (h₂ : trans l (k x) u) :
    trans l (t >>= k) u := by
  unfold trans at *
  rw [← fold_unfold t]
  generalize t.unfold = T at h₁
  generalize hl : Label.val x = lv at h₁
  generalize hs : (CTree.stuck : CTree E B X) = s at h₁
  induction h₁ with
  | br x _ ih => simp only [fold_unfold] at ih; simpa using Trans_.br x (ih hl hs)
  | guard _ ih => simp only [fold_unfold] at ih; simpa using Trans_.guard (ih hl hs)
  | step => cases hl
  | obs => cases hl
  | val => cases val_eq_inv hl; simpa using h₂

theorem isStuck_bind (h : isStuck t) : isStuck (t >>= k) := by
  intro l u hu
  rcases trans_bind_inv hu with ⟨_, _, h', _⟩ | ⟨_, h', _⟩
  · exact h _ _ h'
  · exact h _ _ h'

/-! ### `wtrans` and `bind` -/

theorem etrans_bind_inv (h : etrans l (t >>= k) u) :
    (¬ IsVal l ∧ ∃ t', etrans l t t' ∧ u = t' >>= k) ∨
      (∃ x, trans (.val x) t .stuck ∧ etrans l (k x) u) := by
  rcases etrans_case h with h | ⟨rfl, rfl⟩
  · rcases trans_bind_inv h with ⟨hl, t', g, rfl⟩ | ⟨x, h₁, h₂⟩
    · exact .inl ⟨hl, t', trans_etrans g, rfl⟩
    · exact .inr ⟨x, h₁, trans_etrans h₂⟩
  · exact .inl ⟨isVal_tau, t, enil, rfl⟩

theorem transs_bind_inv (h : Star (trans .tau) (t >>= k) u) :
    (∃ t', Star (trans .tau) t t' ∧ u = t' >>= k) ∨
      (∃ x, wtrans (.val x) t .stuck ∧ Star (trans .tau) (k x) u) := by
  induction h with
  | refl => exact .inl ⟨t, .refl, rfl⟩
  | tail _ hvu ih =>
    rcases ih with ⟨t', h₁, rfl⟩ | ⟨x, h₁, h₂⟩
    · rcases trans_bind_inv hvu with ⟨-, t'', h₂, rfl⟩ | ⟨x, h₂, h₃⟩
      · exact .inl ⟨t'', h₁.tail h₂, rfl⟩
      · exact .inr ⟨x, ⟨t', _, h₁, h₂, .refl⟩, .single h₃⟩
    · exact .inr ⟨x, h₁, h₂.tail hvu⟩

theorem wtrans_bind_inv (h : wtrans l (t >>= k) u) :
    (¬ IsVal l ∧ ∃ t', wtrans l t t' ∧ u = t' >>= k) ∨
      (∃ x, wtrans (.val x) t .stuck ∧ wtrans l (k x) u) ∨
      (∃ x s, wtrans l t s ∧ trans (.val x) s .stuck ∧ wtrans .tau (k x) u) := by
  obtain ⟨t₂, t₁, h₁, h₂, h₃⟩ := h
  rcases transs_bind_inv h₁ with ⟨u₁, g₁, rfl⟩ | ⟨x, g₁, g₁'⟩
  · rcases etrans_bind_inv h₂ with ⟨hl, u₂, g₂, rfl⟩ | ⟨x, g₂, g₂'⟩
    · rcases transs_bind_inv h₃ with ⟨u₃, g₃, rfl⟩ | ⟨x, g₃, g₃'⟩
      · exact .inl ⟨hl, u₃, ⟨u₁, u₂, g₁, g₂, g₃⟩, rfl⟩
      · obtain ⟨u₃, h₄, h₅⟩ := wtrans_val_inv g₃
        exact .inr (.inr ⟨x, u₃, wsnocs ⟨u₁, u₂, g₁, g₂, .refl⟩ h₄, h₅, wtrans_τ.2 g₃'⟩)
    · exact .inr (.inl ⟨x, ⟨u₁, _, g₁, g₂, .refl⟩, ⟨k x, t₁, .refl, g₂', h₃⟩⟩)
  · exact .inr (.inl ⟨x, g₁, ⟨t₂, t₁, g₁', h₂, h₃⟩⟩)

theorem etrans_bind_l {u : CTree E B X} (hl : ¬ IsVal l) (h : etrans l t u) :
    etrans l (t >>= k) (u >>= k) := by
  rcases etrans_case h with h | ⟨rfl, rfl⟩
  · exact trans_etrans (trans_bind_l hl h)
  · exact enil

theorem transs_bind_l {u : CTree E B X} (h : Star (trans .tau) t u) :
    Star (trans .tau) (t >>= k) (u >>= k) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (trans_bind_l isVal_tau h)

theorem wtrans_bind_l {u : CTree E B X} (hl : ¬ IsVal l) (h : wtrans l t u) :
    wtrans l (t >>= k) (u >>= k) :=
  let ⟨_, _, h₁, h₂, h₃⟩ := h
  ⟨_, _, transs_bind_l h₁, etrans_bind_l hl h₂, transs_bind_l h₃⟩

end Bind

section Cases
variable {l : Label E} {t u : CTree E B X}

theorem wtrans_case (h : wtrans l t u) :
    t = u ∨ (∃ v, trans l t v ∧ wtrans .tau v u) ∨ (∃ v, trans .tau t v ∧ wtrans l v u) := by
  obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := h
  rcases h₁.cases_head with rfl | ⟨v, hv, h₁⟩
  · rcases etrans_case h₂ with h₂ | ⟨rfl, rfl⟩
    · exact .inr (.inl ⟨t₂, h₂, wtrans_τ.2 h₃⟩)
    · rcases h₃.cases_head with rfl | ⟨v, hv, h₃⟩
      · exact .inl rfl
      · exact .inr (.inl ⟨v, hv, wtrans_τ.2 h₃⟩)
  · exact .inr (.inr ⟨v, hv, ⟨t₁, t₂, h₁, h₂, h₃⟩⟩)

theorem wtrans_case' (h : wtrans l t u) :
    match l with
    | .tau => t = u ∨ ∃ v, trans .tau t v ∧ wtrans .tau v u
    | _ => (∃ v, trans l t v ∧ wtrans .tau v u) ∨ (∃ v, trans .tau t v ∧ wtrans l v u) := by
  obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := h
  rcases h₁.cases_head with rfl | ⟨v, hv, h₁⟩
  · rcases etrans_case h₂ with h₂ | ⟨rfl, rfl⟩
    · cases l
      · exact .inr ⟨t₂, h₂, wtrans_τ.2 h₃⟩
      all_goals exact .inl ⟨t₂, h₂, wtrans_τ.2 h₃⟩
    · rcases h₃.cases_head with rfl | ⟨v, hv, h₃⟩
      · exact .inl rfl
      · exact .inr ⟨v, hv, wtrans_τ.2 h₃⟩
  · have hw : wtrans l v u := ⟨t₁, t₂, h₁, h₂, h₃⟩
    cases l <;> exact .inr ⟨v, hv, hw⟩

theorem pwtrans_case (h : pwtrans l t u) :
    (∃ v, trans l t v ∧ wtrans .tau v u) ∨ (∃ v, trans .tau t v ∧ wtrans l v u) := by
  obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := h
  rcases h₁.cases_head with rfl | ⟨v, hv, h₁⟩
  · exact .inl ⟨t₂, h₂, wtrans_τ.2 h₃⟩
  · exact .inr ⟨v, hv, ⟨t₁, t₂, h₁, trans_etrans h₂, h₃⟩⟩

theorem wtrans_stuck_inv (h : wtrans l (.stuck : CTree E B X) t) :
    match l with
    | .tau => t = .stuck
    | _ => False := by
  obtain ⟨rfl, rfl⟩ := wtrans_isStuck_inv stuck_isStuck h
  rfl

end Cases

section BindR
variable {l : Label E} {t : CTree E B X} {k : X → CTree E B Y} {u : CTree E B Y} {x : X}

/-- Two cases are needed: if `t = guard (pure x)` and `u = k x`, the `guard` can be processed by
taking the `pure` in the prefix, but cannot be processed to reach `u` in the bound computation. -/
theorem wtrans_bind_r (h₁ : wtrans (.val x) t .stuck) (h₂ : wtrans l (k x) u) :
    u = k x ∨ wtrans l (t >>= k) u := by
  obtain ⟨t', h₁, h₁'⟩ := wtrans_val_inv h₁
  have h₁ := wtrans_bind_l (k := k) isVal_tau h₁
  rcases wtrans_case h₂ with rfl | ⟨v, h₃, h₄⟩ | ⟨v, h₃, h₄⟩
  · exact .inl rfl
  · exact .inr (wconss h₁ (wsnocs (trans_wtrans (trans_bind_r h₁' h₃)) h₄))
  · exact .inr (wconss h₁ (wconss (trans_wtrans (trans_bind_r h₁' h₃)) h₄))

theorem wtrans_bind_r' (h₁ : wtrans (.val x) t .stuck) (h₂ : pwtrans l (k x) u) :
    wtrans l (t >>= k) u := by
  obtain ⟨t', h₁, h₁'⟩ := wtrans_val_inv h₁
  have h₁ := wtrans_bind_l (k := k) isVal_tau h₁
  rcases pwtrans_case h₂ with ⟨v, h₃, h₄⟩ | ⟨v, h₃, h₄⟩
  · exact wconss h₁ (wsnocs (trans_wtrans (trans_bind_r h₁' h₃)) h₄)
  · exact wconss h₁ (wconss (trans_wtrans (trans_bind_r h₁' h₃)) h₄)

theorem wtrans_bind_lr {t u : CTree E B X} {v : CTree E B Y} (h₁ : pwtrans l t u)
    (h₂ : wtrans (.val x) u .stuck) (h₃ : pwtrans .tau (k x) v) : wtrans l (t >>= k) v := by
  obtain ⟨t₁, t₂, h₁, h₁', h₁''⟩ := h₁
  have hl : ¬ IsVal l := by
    rintro ⟨y⟩
    cases trans_val_inv h₁'
    cases transs_isStuck_inv stuck_isStuck h₁''
    cases (wtrans_isStuck_inv stuck_isStuck h₂).1
  refine ⟨_, t₂ >>= k, transs_bind_l h₁, trans_etrans (trans_bind_l hl h₁'), ?_⟩
  exact wtrans_τ.1 (wconss (wtrans_bind_l isVal_tau (wtrans_τ.2 h₁''))
    (wtrans_bind_r' h₂ h₃))

end BindR

/-! ## Triggers -/

section Trigger
variable {e : E.I} {k : E.O e → CTree E B Y}

theorem trans_trigger (x : E.O e) : trans (.obs e x) (CTree.trigger e >>= k) (k x) := by
  rw [bind_trigger]; exact trans_vis x k

theorem trans_trigger' (x : E.O e) (t : CTree E B Y) :
    trans (.obs e x) (CTree.trigger e >>= fun _ => t) t :=
  trans_trigger (k := fun _ => t) x

theorem trans_trigger_inv {l : Label E} {u : CTree E B Y}
    (h : trans l (CTree.trigger e >>= k) u) : ∃ x, u = k x ∧ l = .obs e x := by
  rw [bind_trigger] at h; exact trans_vis_inv h

theorem trans_branch {l : Label E} {c : B.I} {k : B.O c → CTree E B X} {t' : CTree E B X}
    (x : B.O c) (h : trans l (k x) t') : trans l (CTree.branch c >>= k) t' := by
  rw [bind_branch]; exact trans_br x h

end Trigger

/-! ## Well-formed labels

`WfVal X l`: if `l` is a value label, its value has type `X`. -/

def WfVal (X : Type u) (l : Label E) : Prop := ∀ (Y : Type u) (v : Y), l = .val v → X = Y

theorem wfVal_val (v : X) : WfVal X (.val v : Label E) := fun _ _ h => val_eq_invT h

theorem wfVal_nonval {l : Label E} (h : ¬ IsVal l) : WfVal X l :=
  fun _ _ e => (h (e ▸ .val _)).elim

theorem wfVal_trans {l : Label E} {t t' : CTree E B X} (h : trans l t t') : WfVal X l := by
  rintro Y v rfl; exact trans_val_invT h

theorem wfVal_isVal_inv {l : Label E} (hv : IsVal l) (hw : WfVal X l) : ∃ x : X, l = .val x := by
  cases hv with
  | val x => cases hw _ x rfl; exact ⟨x, rfl⟩

end CTree
