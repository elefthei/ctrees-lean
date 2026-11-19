/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.SSimAlt
public import CTree.Eq.SBisim
public import CTree.Eq.SBisimAlt

/-!
# Facts about `iter`

Unfolding of the guarded `CTree.iter`, its compatibility with strong (bi)simulation, and the
naturality and codiagonal laws of iteration (← `Eq/IterFacts.v`). `CTree` is extensional, so the
Rocq `Proper (equ …)` instances `iter_gen_equ` and `iter_equ` are omitted.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E F C D : Effect.{u}}

/-- One unfolding of `iter step`, starting from an arbitrary first step `t`. -/
def iter_gen {I X : Type u} (step : I → CTree E C (I ⊕ X)) (t : CTree E C (I ⊕ X)) :
    CTree E C X :=
  t >>= fun | .inl i => .guard (CTree.iter step i) | .inr x => pure x

theorem iter_iter_gen {I X : Type u} (i : I) (step : I → CTree E C (I ⊕ X)) :
    CTree.iter step i = iter_gen step (step i) := by
  rw [unfold_iter, iter_gen]; congr; funext x; cases x <;> rfl

/-- Bisimulation-up-to-`bind` principle for equality: two continuations that agree or produce
guards over further binds with the same continuations give equal binds. -/
private theorem eq_bind_coind {A Z : Type u} (K₁ K₂ : A → CTree E C Z)
    (h : ∀ x, K₁ x = K₂ x ∨ ∃ s, K₁ x = .guard (s >>= K₁) ∧ K₂ x = .guard (s >>= K₂)) :
    ∀ s : CTree E C A, s >>= K₁ = s >>= K₂ := by
  intro s
  refine eq_coind_upto (fun t u => ∃ s, t = s >>= K₁ ∧ u = s >>= K₂) ?_ _ _ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨s, rfl, rfl⟩
  cases s with
  | ret x =>
    simp only [pure_bind]
    rcases h x with hx | ⟨s', h₁, h₂⟩
    · rw [hx]; exact EqF.refl (fun _ => .inr rfl) _
    · rw [h₁, h₂]; simp only [unfold_guard]; exact .guard (.inl ⟨s', rfl, rfl⟩)
  | stuck => simp only [stuck_bind, unfold_stuck]; exact .stuck
  | step t => simp only [step_bind, unfold_step]; exact .step (.inl ⟨t, rfl, rfl⟩)
  | guard t => simp only [guard_bind, unfold_guard]; exact .guard (.inl ⟨t, rfl, rfl⟩)
  | vis e k => simp only [vis_bind, unfold_vis]; exact .vis e fun x => .inl ⟨k x, rfl, rfl⟩
  | br c k => simp only [br_bind, unfold_br]; exact .br c fun x => .inl ⟨k x, rfl, rfl⟩

/-- Thanks to `SSimAlt`, this proof does not need a helper inductive. -/
theorem ssim_iter {A A' B B' : Type u} (L : Label E → Label F → Prop) (Ra : A → A' → Prop)
    (Rb : B → B' → Prop) {L0 : Label E → Label F → Prop}
    (HL0 : isUpdateValRel L (sumRel Ra Rb) L0)
    (HRb : ∀ b b', Rb b b' ↔ L (.val b) (.val b'))
    (step : A → CTree E C (A ⊕ B)) (step' : A' → CTree F D (A' ⊕ B'))
    (hstep : ∀ a a', Ra a a' → ssim L0 (step a) (step' a')) :
    ∀ a a', Ra a a' → ssim L (CTree.iter step a) (CTree.iter step' a') := by
  intro a a' ha
  refine ssim_ssim'.2 (coinduction (b := ss' L)
    (fun p : {p : A × A' // Ra p.1 p.2} => CTree.iter step p.1.1)
    (fun p => CTree.iter step' p.1.2) ?_ ⟨(a, a'), ha⟩)
  rintro R hR CH ⟨⟨a, a'⟩, ha⟩
  show ss' L R (CTree.iter step a) (CTree.iter step' a')
  rw [unfold_iter, unfold_iter]
  refine ss'_chain_bind_gen HL0 (.step hR) _ _ _ _ (hstep a a' ha) ?_
  rintro (x | x) (y | y) h
  · exact step_ss'_guard (CH ⟨(x, y), h⟩)
  · exact h.elim
  · exact h.elim
  · exact step_ssbt'_ret hR ((HRb x y).1 h)

private theorem sumRel_eq {X Y : Type u} : sumRel (@Eq X) (@Eq Y) = Eq := by
  funext a b; cases a <;> cases b <;> simp [sumRel]

private theorem val_eq_iff {Y : Type u} (b b' : Y) : b = b' ↔ (.val b : Label E) = .val b' :=
  ⟨fun h => h ▸ rfl, fun h => by injection h⟩

/-- `iter` preserves `≲` pointwise (Rocq instance `ssim_eq_iter`). -/
theorem ssim_eq_iter {X Y : Type u} {step step' : X → CTree E C (X ⊕ Y)}
    (h : ∀ x, step x ≲ step' x) (x : X) : CTree.iter step x ≲ CTree.iter step' x :=
  ssim_iter (L := Eq) (L0 := Eq) Eq Eq (sumRel_eq (X := X) (Y := Y) ▸ updateValRel_eq) val_eq_iff
    step step' (by rintro a _ rfl; exact h a) x x rfl

theorem iter_natural_ctree {X Y Z : Type u} (f : X → CTree E C (X ⊕ Y)) (g : Y → CTree E C Z)
    (a : X) :
    CTree.iter f a >>= g =
      CTree.iter (fun x => f x >>= fun
        | .inl a => pure (.inl a)
        | .inr b => g b >>= fun z => pure (.inr z)) a := by
  let K₁ : X ⊕ Y → CTree E C Z := fun
    | .inl l => .guard (CTree.iter f l >>= g) | .inr r => g r
  let G := fun x => f x >>= fun
    | .inl a => (pure (.inl a) : CTree E C (X ⊕ Z)) | .inr b => g b >>= fun z => pure (.inr z)
  let K₂ : X ⊕ Y → CTree E C Z := fun
    | .inl l => .guard (CTree.iter G l) | .inr r => g r
  have hl : ∀ a, CTree.iter f a >>= g = f a >>= K₁ := fun a => by
    rw [unfold_iter, bind_assoc]; congr; funext x; cases x <;> simp [K₁]
  have hr : ∀ a, CTree.iter G a = f a >>= K₂ := fun a => by
    rw [unfold_iter, bind_assoc]; congr; funext x; cases x <;> simp [K₂]
  show _ = CTree.iter G a
  rw [hl, hr]
  refine eq_bind_coind K₁ K₂ (fun x => ?_) _
  cases x with
  | inl l => exact .inr ⟨f l, by show CTree.guard _ = _; rw [hl], by show CTree.guard _ = _; rw [hr]⟩
  | inr r => exact .inl rfl

theorem iter_codiagonal_ctree {A B : Type u} (f : A → CTree E C (A ⊕ (A ⊕ B))) (a : A) :
    CTree.iter (CTree.iter f) a =
      CTree.iter (fun x => f x >>= fun
        | .inl a => pure (.inl a)
        | .inr b => pure b) a := by
  let G : A → CTree E C (A ⊕ B) := fun x => f x >>= fun
    | .inl a => pure (.inl a) | .inr b => pure b
  let K₁ : A ⊕ (A ⊕ B) → CTree E C B := fun
    | .inl l => .guard (CTree.iter (CTree.iter f) l)
    | .inr (.inl l) => .guard (CTree.iter (CTree.iter f) l)
    | .inr (.inr b) => pure b
  let K₂ : A ⊕ (A ⊕ B) → CTree E C B := fun
    | .inl l => .guard (CTree.iter G l)
    | .inr (.inl l) => .guard (CTree.iter G l)
    | .inr (.inr b) => pure b
  have hl : ∀ a, CTree.iter (CTree.iter f) a = f a >>= K₁ := fun a => by
    rw [unfold_iter, unfold_iter, bind_assoc]; congr; funext x
    rcases x with l | l | b
    · simp only [guard_bind, K₁]
      rw [unfold_iter (CTree.iter f) l]
    · simp [K₁]
    · simp [K₁]
  have hr : ∀ a, CTree.iter G a = f a >>= K₂ := fun a => by
    rw [unfold_iter, bind_assoc]; congr; funext x; rcases x with l | l | b <;> simp [K₂]
  show _ = CTree.iter G a
  rw [hl, hr]
  refine eq_bind_coind K₁ K₂ (fun x => ?_) _
  rcases x with l | l | b
  · exact .inr ⟨f l, by show CTree.guard _ = _; rw [hl], by show CTree.guard _ = _; rw [hr]⟩
  · exact .inr ⟨f l, by show CTree.guard _ = _; rw [hl], by show CTree.guard _ = _; rw [hr]⟩
  · exact .inl rfl

theorem sbisim_iter {A A' B B' : Type u} (L : Label E → Label F → Prop) (Ra : A → A' → Prop)
    (Rb : B → B' → Prop) {L0 : Label E → Label F → Prop}
    (HL0 : isUpdateValRel L (sumRel Ra Rb) L0)
    (HRb : ∀ b b', Rb b b' ↔ L (.val b) (.val b'))
    (step : A → CTree E C (A ⊕ B)) (step' : A' → CTree F D (A' ⊕ B'))
    (hstep : ∀ a a', Ra a a' → sbisim L0 (step a) (step' a')) :
    ∀ a a', Ra a a' → sbisim L (CTree.iter step a) (CTree.iter step' a') := by
  intro a a' ha
  refine sbisim_sbisim'.2 fun side => coinduction₃ (b := sb' L)
    (fun p : Bool × {p : A × A' // Ra p.1 p.2} => p.1)
    (fun p => CTree.iter step p.2.1.1) (fun p => CTree.iter step' p.2.1.2) ?_ (side, ⟨(a, a'), ha⟩)
  rintro R hR CH ⟨side, ⟨a, a'⟩, ha⟩
  show sb' L R side (CTree.iter step a) (CTree.iter step' a')
  rw [unfold_iter, unfold_iter]
  refine sbt'_clo_bind_gen HL0 hR (sbisim_sbisim'.1 (hstep a a' ha) side) ?_
  rintro (x | x) (y | y) h b
  · exact step_sb'_guard (CH (b, ⟨(x, y), h⟩))
  · exact h.elim
  · exact h.elim
  · exact step_sb'_ret ((HRb x y).1 h) (fun s => b_chain hR s _ _ (sb'_stuck s)) b

/-- `iter` preserves `~` pointwise (Rocq instance `sbisim_eq_iter`). -/
theorem sbisim_eq_iter {X Y : Type u} {step step' : X → CTree E C (X ⊕ Y)}
    (h : ∀ x, step x ~ step' x) (x : X) : CTree.iter step x ~ CTree.iter step' x :=
  sbisim_iter (L := Eq) (L0 := Eq) Eq Eq (sumRel_eq (X := X) (Y := Y) ▸ updateValRel_eq) val_eq_iff
    step step' (by rintro a _ rfl; exact h a) x x rfl

theorem iter_dinatural_ctree_inner {X Y Z : Type u} (f : X → CTree E C (Y ⊕ Z))
    (g : Y → CTree E C (X ⊕ Z)) (x : X) :
    (CTree.iter (fun x => f x >>= fun
        | .inl y => g y
        | .inr z => pure (.inr z)) x : CTree E C Z) ~
      f x >>= fun
        | .inl y => .guard (CTree.iter (fun y => g y >>= fun
            | .inl x => f x
            | .inr z => pure (.inr z)) y)
        | .inr z => pure z := by
  refine sbisim_sbisim'.2 fun side => coinduction₃ (b := sb' Eq)
    (fun p : Bool × X => p.1) (fun p => CTree.iter _ p.2) (fun p => f p.2 >>= _) ?_ (side, x)
  rintro R hR CH ⟨side, x⟩
  have hlp : ∀ (t : CTree E C (X ⊕ Z)) (K₁ K₂ : X ⊕ Z → CTree E C Z),
      (∀ r b, R b (K₁ r) (K₂ r)) → ∀ b, R b (t >>= K₁) (t >>= K₂) :=
    fun t _ _ h b => st'_clo_bind_eq hR (refl_sbisim' (fun _ => rfl) t b) h
  have hk : ∀ (r : X ⊕ Z) b, R b
      ((fun | .inl l => .guard (CTree.iter (fun x => f x >>= fun
          | .inl y => g y
          | .inr z => pure (.inr z)) l) | .inr r => pure r) r)
      ((fun r => (match r with | .inl x => f x | .inr z => pure (.inr z)) >>= fun
        | .inl y => .guard (CTree.iter (fun y => g y >>= fun
            | .inl x => f x
            | .inr z => pure (.inr z)) y)
        | .inr z => pure z) r) := by
    rintro (x' | z) b
    · exact step_sb'_guard_l' hR (fun s => CH (s, x')) b
    · simp only [pure_bind]; exact step_sbt'_ret hR rfl b
  show sb' Eq R side _ _
  rw [iter_iter_gen, iter_gen, bind_assoc]
  refine sbt'_clo_bind_eq hR (refl_sbisim' (fun _ => rfl) (f x) side) ?_
  rintro (y | z) b
  · simp only
    rw [iter_iter_gen, iter_gen, bind_assoc]
    cases g y with
    | ret r =>
      cases r with
      | inl x' =>
        simp only [pure_bind]
        exact step_sb'_guard (CH (b, x'))
      | inr z =>
        simp only [pure_bind]
        exact step_sb'_guard_r hR
          (step_sb'_ret rfl (fun s => b_chain hR s _ _ (sb'_stuck s)) b)
    | stuck =>
      simp only [stuck_bind]
      exact step_sb'_guard_r hR (sb'_stuck b)
    | step t =>
      simp only [step_bind]
      exact step_sb'_guard_r hR (step_sb'_step rfl (hlp t _ _ hk) b)
    | guard t =>
      simp only [guard_bind]
      exact step_sb'_guard (step_sb'_guard_r' hR (hlp t _ _ hk) b)
    | vis e k =>
      simp only [vis_bind]
      exact step_sb'_guard_r hR (step_sb'_vis_id rfl (fun v => ⟨fun s => hlp (k v) _ _ hk s, rfl⟩) b)
    | br c k =>
      simp only [br_bind]
      exact step_sb'_guard_r hR (step_sb'_br_id rfl (fun v => hlp (k v) _ _ hk b))
  · simp only [pure_bind]
    exact step_sb'_ret rfl (fun s => b_chain hR s _ _ (sb'_stuck s)) b

theorem iter_dinatural_ctree {X Y Z : Type u} (f : X → CTree E C (Y ⊕ Z))
    (g : Y → CTree E C (X ⊕ Z)) (x : X) :
    (CTree.iter (fun x => f x >>= fun
        | .inl y => g y
        | .inr z => pure (.inr z)) x : CTree E C Z) ~
      f x >>= fun
        | .inl y => CTree.iter (fun y => g y >>= fun
            | .inl x => f x
            | .inr z => pure (.inr z)) y
        | .inr z => pure z :=
  sbisim_trans (iter_dinatural_ctree_inner f g x) (sbisim_bind_eq (f x) fun
    | .inl _ => sb_guard _
    | .inr _ => sbisim_refl _)

end CTree
