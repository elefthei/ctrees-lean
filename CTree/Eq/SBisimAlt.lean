/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.SSimAlt
public import CTree.Misc.Pure

/-!
# An alternative strong bisimulation

`sb' L` is a `Bool`-indexed strong bisimulation functor built on `ss'_gen`: side `true` plays
the left tree, side `false` the right one. As for `ss'`, the challenge does not go through the
inductive `trans` relation, so `br`/`guard` nodes allow a coinductive step. Its greatest fixpoint
`sbisim'` coincides with `sbisim` (`sbisim_sbisim'`) (← `Eq/SBisimAlt.v`). `CTree` is
extensional, so the Rocq up-to-`equ` closures and `Proper` instances are omitted.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinduction

variable {E F C D : Effect.{u}} {X Y X' Y' : Type u}

/-- Changes the label relation and both relations of `ss'_gen` at once. -/
theorem ss'_gen_imp {L L' : Label E → Label F → Prop}
    {R R' Reps Reps' : Rel (CTree E C X) (CTree F D Y)} {t : CTree E C X} {u : CTree F D Y}
    (hL : ∀ l l', L l l' → L' l l') (hR : ∀ t u, R t u → R' t u)
    (hReps : ∀ t u, Reps t u → Reps' t u) (h : ss'_gen L R Reps t u) : ss'_gen L' R' Reps' t u :=
  ⟨fun hp l t' ht =>
    let ⟨l', u', h₁, h₂, h₃⟩ := h.1 hp l t' ht
    ⟨l', u', h₁, hR _ _ h₂, hL _ _ h₃⟩,
   (ss'_gen_mon (L := L) (fun _ _ h => hR _ _ h) (fun _ _ h => hReps _ _ h) h).2⟩

/-- The alternative strong bisimulation functor. -/
def sb' (L : Label E → Label F → Prop) : Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R side t u :=
    (side = true → ss'_gen L (fun t u => ∀ s, R s t u) (R true) t u) ∧
    (side = false → ss'_gen (flip L) (fun u t => ∀ s, R s t u) (flip (R false)) u t)
  mono h _ _ _ H :=
    ⟨fun hs => ss'_gen_imp (fun _ _ h => h) (fun _ _ h' s => h s _ _ (h' s)) (fun _ _ => h true _ _)
      (H.1 hs),
     fun hs => ss'_gen_imp (fun _ _ h => h) (fun _ _ h' s => h s _ _ (h' s))
      (fun _ _ => h false _ _) (H.2 hs)⟩

/-! ## Symmetry -/

/-- The `true` half of `sb'`. -/
def sb'l (L : Label E → Label F → Prop) : Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R side t u := side = true → sb' L R side t u
  mono h side t u H hs := (sb' L).mono h side t u (H hs)

/-- Converse that also negates the side. -/
def converseNeg (α : Type u) : Mon (Rel3 Bool α α) :=
  ⟨fun R b x y => R (!b) y x, fun h b x y => h (!b) y x⟩

theorem converseNeg_invol {α : Type u} (R : Rel3 Bool α α) : converseNeg α (converseNeg α R) = R :=
  funext fun b => funext fun x => funext fun y => by
    show R (!!b) x y = R b x y
    rw [Bool.not_not]

theorem sbisim'_sym {L : Label E → Label E → Prop} (hL : ∀ l l', L l l' → L l' l) :
    Symmetrical (converseNeg _) (sb' L : Mon (Rel3 Bool (CTree E C X) (CTree E C X))) (sb'l L) where
  invol := converseNeg_invol
  eq R := funext fun s => funext fun t => funext fun u => propext <| by
    show sb' L R s t u ↔ cap (sb'l L R) (converseNeg _ (sb'l L (converseNeg _ R))) s t u
    rw [Rel3.cap_apply]
    cases s with
    | true => exact ⟨fun h => ⟨fun _ => h, nofun⟩, fun h => h.1 rfl⟩
    | false =>
      refine ⟨fun h => ⟨nofun, fun _ => ⟨fun _ => ?_, nofun⟩⟩, fun h => ⟨nofun, fun _ => ?_⟩⟩
      · exact ss'_gen_imp (fun _ _ h => hL _ _ h) (fun _ _ h s => h (!s)) (fun _ _ h => h)
          (h.2 rfl)
      · exact ss'_gen_imp (fun _ _ h => hL _ _ h)
          (fun _ _ h s => by simpa [converseNeg] using h (!s)) (fun _ _ h => h)
          ((h.2 rfl).1 rfl)

theorem sb'_flip {L : Label E → Label F → Prop} {R : Rel3 Bool (CTree E C X) (CTree F D Y)}
    {side : Bool} {t : CTree E C X} {u : CTree F D Y}
    (h : sb' (flip L) (fun b => flip (R (!b))) (!side) u t) : sb' L R side t u := by
  cases side
  · exact ⟨nofun, fun _ => ss'_gen_imp (fun _ _ h => h)
      (fun _ _ h s => by simpa [flip] using h (!s))
      (fun _ _ h => h) (h.1 rfl)⟩
  · exact ⟨fun _ => ss'_gen_imp (fun _ _ h => h) (fun _ _ h s => by simpa [flip] using h (!s))
      (fun _ _ h => h) (h.2 rfl), nofun⟩

/-- The alternative strong bisimulation: both sides of `gfp (sb' L)`. -/
def sbisim' (L : Label E → Label F → Prop) (t : CTree E C X) (u : CTree F D Y) : Prop :=
  ∀ side, gfp (sb' L) side t u

theorem gfp_sb'_unfold {L : Label E → Label F → Prop} {side : Bool} {t : CTree E C X}
    {u : CTree F D Y} : gfp (sb' L) side t u ↔ sb' L (gfp (sb' L)) side t u :=
  ⟨fun h => gfp_pfp (b := sb' L) side t u h, fun h => b_chain (gfp_chain (sb' L)) side t u h⟩

/-! ## Homogeneous theory -/

section Homogeneous
variable {L : Label E → Label E → Prop} {R : Rel3 Bool (CTree E C X) (CTree E C X)}

theorem refl_sb' (hL : ∀ l, L l l) (hR : Chain (sb' L) R) : ∀ side t, R side t t :=
  tower (P := fun R : Rel3 Bool (CTree E C X) (CTree E C X) => ∀ side t, R side t t)
    (infClosed_forall fun s => infClosed_forall fun t => Rel3.infClosed_apply s t t)
    (fun R _ ih _ t => show sb' L R _ t t from
      ⟨fun _ => ss'_gen_refl (fun t s => ih s t) (ih true) hL t,
       fun _ => ss'_gen_refl (L := flip L) (R := fun u t => ∀ s, R s t u)
        (Reps := flip (R false)) (fun t s => ih s t) (fun t => ih false t) hL t⟩) R hR

theorem refl_bsb' (hL : ∀ l, L l l) (hR : Chain (sb' L) R) : ∀ side t, sb' L R side t t :=
  refl_sb' hL (.step hR)

theorem refl_sbisim' (hL : ∀ l, L l l) (t : CTree E C X) : sbisim' L t t :=
  fun s => refl_sb' hL (gfp_chain _) s t

theorem sym_sb (hL : ∀ l l', L l l' → L l' l) (hR : Chain (sb' L) R) :
    ∀ side x y, R (!side) x y → R side y x := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X) (CTree E C X) =>
    ∀ side x y, R (!side) x y → R side y x) ?_ ?_ R hR
  · intro T hT s x y h
    exact Rel3.inf_apply.2 fun R hR => hT R hR s x y (Rel3.inf_apply.1 h R hR)
  · intro R _ ih side x y H
    cases side
    · exact ⟨nofun, fun _ => ss'_gen_imp (fun _ _ h => hL _ _ h) (fun _ _ h s => ih s _ _ (h (!s)))
        (fun _ _ h => ih false _ _ h) (H.1 rfl)⟩
    · exact ⟨fun _ => ss'_gen_imp (fun _ _ h => hL _ _ h) (fun _ _ h s => ih s _ _ (h (!s)))
        (fun _ _ h => ih true _ _ h) (H.2 rfl), nofun⟩

theorem st'_flip (hL : ∀ l l', L l l' → L l' l) (hR : Chain (sb' L) R) {b : Bool}
    {t u : CTree E C X} : R b t u ↔ R (!b) u t :=
  ⟨fun h => sym_sb hL hR (!b) t u (by simpa using h), sym_sb hL hR b u t⟩

theorem sbisim_flip (hL : ∀ l l', L l l' → L l' l) {t u : CTree E C X} (h : sbisim' L t u) :
    sbisim' L u t :=
  fun s => (st'_flip hL (gfp_chain _)).2 (by simpa using h (!s))

end Homogeneous

theorem split_st' {L : Label E → Label E → Prop} (hL : ∀ l l', L l l' → L l' l)
    {R : Rel3 Bool (CTree E C X) (CTree E C X)} (hR : Chain (sb' L) R) {t u : CTree E C X} :
    (∀ side, R side t u) ↔ R true t u ∧ R true u t :=
  ⟨fun h => ⟨h true, (st'_flip hL hR).2 (h false)⟩,
   fun h side => by
    cases side
    · exact (st'_flip hL hR).2 h.2
    · exact h.1⟩

theorem split_st'_eq {R : Rel3 Bool (CTree E C X) (CTree E C X)} (hR : Chain (sb' Eq) R)
    {t u : CTree E C X} : (∀ side, R side t u) ↔ R true t u ∧ R true u t :=
  split_st' (fun _ _ h => h.symm) hR

/-! ## Heterogeneous theory -/

section Heterogeneous
variable {L : Label E → Label F → Prop} {R : Rel3 Bool (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem sb'_true_ss' :
    sb' L R true t u ↔ ss'_gen L (fun t u => ∀ side, R side t u) (R true) t u :=
  ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, nofun⟩⟩

theorem sb'_false_ss' :
    sb' L R false t u ↔ ss'_gen (flip L) (fun u t => ∀ side, R side t u) (flip (R false)) u t :=
  ⟨fun h => h.2 rfl, fun h => ⟨nofun, fun _ => h⟩⟩

theorem sb'_true_stuck : sb' L R true (.stuck : CTree E C X) u := sb'_true_ss'.2 ss'_stuck

theorem sb'_stuck (side : Bool) : sb' L R side (.stuck : CTree E C X) (.stuck : CTree F D Y) := by
  cases side
  · exact sb'_flip sb'_true_stuck
  · exact sb'_true_stuck

end Heterogeneous

/-! ## Proof rules -/

section ProofRules
variable {L : Label E → Label F → Prop} {R : Rel3 Bool (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem step_sb'_ret {x : X} {y : Y} (hL : L (.val x) (.val y))
    (hst : ∀ side, R side .stuck .stuck) :
    ∀ side, sb' L R side (pure x : CTree E C X) (pure y : CTree F D Y) :=
  fun _ => ⟨fun _ => step_ss'_ret hst hL, fun _ => step_ss'_ret hst hL⟩

theorem step_sbt'_ret (hR : Chain (sb' L) R) {x : X} {y : Y} (hL : L (.val x) (.val y)) :
    ∀ side, R side (pure x : CTree E C X) (pure y : CTree F D Y) :=
  fun side => b_chain hR side _ _
    (step_sb'_ret hL (fun s => b_chain hR s _ _ (sb'_stuck s)) side)

/-- Visible events are deterministic for the LTS: the itree-style rule. -/
theorem step_sb'_vis {e : E.I} {f : F.I} {k : E.O e → CTree E C X} {k' : F.O f → CTree F D Y}
    (h₁ : ∀ x, ∃ y, (∀ side, R side (k x) (k' y)) ∧ L (.obs e x) (.obs f y))
    (h₂ : ∀ y, ∃ x, (∀ side, R side (k x) (k' y)) ∧ L (.obs e x) (.obs f y)) :
    ∀ side, sb' L R side (.vis e k) (.vis f k') :=
  fun _ => ⟨fun _ => step_ss'_vis h₁, fun _ => step_ss'_vis h₂⟩

theorem step_sb'_vis_id {e : E.I} {f : F.I} (hO : F.O f = E.O e) {k : E.O e → CTree E C X}
    {k' : F.O f → CTree F D Y}
    (h : ∀ x, (∀ side, R side (k x) (k' (cast hO.symm x))) ∧
      L (.obs e x) (.obs f (cast hO.symm x))) :
    ∀ side, sb' L R side (.vis e k) (.vis f k') :=
  step_sb'_vis (fun x => ⟨_, h x⟩) fun y => ⟨cast hO y, by
    have := h (cast hO y); rwa [cast_cast, cast_eq] at this⟩

theorem step_sb'_vis_l {e : E.I} {k : E.O e → CTree E C X}
    (h : ∀ x, ∃ l' u', trans l' u u' ∧ (∀ side, R side (k x) u') ∧ L (.obs e x) l') :
    sb' L R true (.vis e k) u :=
  ⟨fun _ => step_ss'_vis_l h, nofun⟩

/-- Delayed nodes allow a coinductive step. -/
theorem step_sb'_guard {side : Bool} (h : R side t u) : sb' L R side (.guard t) (.guard u) :=
  ⟨fun hs => step_ss'_guard (by subst hs; exact h),
   fun hs => step_ss'_guard (by subst hs; exact h)⟩

theorem step_sb'_true_guard_l (_hR : Chain (sb' L) R) (h : R true t u) :
    sb' L R true (.guard t) u :=
  ⟨fun _ => step_ss'_guard_l h, nofun⟩

theorem step_sb'_guard_l (hR : Chain (sb' L) R) {side : Bool} (h : sb' L R side t u) :
    sb' L R side (.guard t) u :=
  ⟨fun hs => step_ss'_guard_l (b_chain hR true _ _ (by subst hs; exact h)),
   fun hs => step_ss'_guard_r (h.2 hs)⟩

theorem step_sb'_false_guard_r (_hR : Chain (sb' L) R) (h : R false t u) :
    sb' L R false t (.guard u) :=
  ⟨nofun, fun _ => step_ss'_guard_l h⟩

theorem step_sb'_guard_r (hR : Chain (sb' L) R) {side : Bool} (h : sb' L R side t u) :
    sb' L R side t (.guard u) :=
  ⟨fun hs => step_ss'_guard_r (h.1 hs),
   fun hs => step_ss'_guard_l (b_chain hR false _ _ (by subst hs; exact h))⟩

theorem step_sb'_br {side : Bool} {a : C.I} {b : D.I} {k : C.O a → CTree E C X}
    {k' : D.O b → CTree F D Y} (h₁ : ∀ x, ∃ y, R side (k x) (k' y))
    (h₂ : ∀ y, ∃ x, R side (k x) (k' y)) : sb' L R side (.br a k) (.br b k') :=
  ⟨fun hs => by subst hs; exact step_ss'_br h₁,
   fun hs => by subst hs; exact step_ss'_br fun y => let ⟨x, h⟩ := h₂ y; ⟨x, h⟩⟩

theorem step_sb'_br_id {side : Bool} {a : C.I} {b : D.I} (hO : D.O b = C.O a)
    {k : C.O a → CTree E C X} {k' : D.O b → CTree F D Y}
    (h : ∀ x, R side (k x) (k' (cast hO.symm x))) : sb' L R side (.br a k) (.br b k') :=
  step_sb'_br (fun x => ⟨_, h x⟩) fun y => ⟨cast hO y, by
    have := h (cast hO y); rwa [cast_cast, cast_eq] at this⟩

theorem step_sb'_true_br_l (_hR : Chain (sb' L) R) {c : C.I} {k : C.O c → CTree E C X}
    (h : ∀ x, R true (k x) u) : sb' L R true (.br c k) u :=
  ⟨fun _ => step_ss'_br_l h, nofun⟩

theorem step_sb'_br_l (hR : Chain (sb' L) R) {side : Bool} {c : C.I} (z : C.O c)
    {k : C.O c → CTree E C X} (h : ∀ x, sb' L R side (k x) u) : sb' L R side (.br c k) u :=
  ⟨fun hs => step_ss'_br_l fun x => b_chain hR true _ _ (by subst hs; exact h x),
   fun hs => step_ss'_br_r z ((h z).2 hs)⟩

theorem step_sb'_step (hL : L .tau .tau) (h : ∀ side, R side t u) :
    ∀ side, sb' L R side (.step t) (.step u) :=
  fun _ => ⟨fun _ => step_ss'_step hL h, fun _ => step_ss'_step hL h⟩

theorem step_sb'_brS (hR : Chain (sb' L) R) {c : C.I} {d : D.I} {k : C.O c → CTree E C X}
    {k' : D.O d → CTree F D Y} (h₁ : ∀ x, ∃ y, ∀ side, R side (k x) (k' y))
    (h₂ : ∀ y, ∃ x, ∀ side, R side (k x) (k' y)) (hL : L .tau .tau) :
    ∀ side, sb' L R side (.brS c k) (.brS d k') :=
  fun side => step_sb'_br
    (fun x => let ⟨y, hy⟩ := h₁ x; ⟨y, b_chain hR side _ _ (step_sb'_step hL hy side)⟩)
    (fun y => let ⟨x, hx⟩ := h₂ y; ⟨x, b_chain hR side _ _ (step_sb'_step hL hx side)⟩)

theorem step_sb'_brS_id (hR : Chain (sb' L) R) {c : C.I} {d : D.I} (hO : D.O d = C.O c)
    {k : C.O c → CTree E C X} {k' : D.O d → CTree F D Y} (hL : L .tau .tau)
    (h : ∀ x side, R side (k x) (k' (cast hO.symm x))) :
    ∀ side, sb' L R side (.brS c k) (.brS d k') :=
  fun side => step_sb'_br_id hO fun x => b_chain hR side _ _ (step_sb'_step hL (h x) side)

theorem step_sb'_true_step_l (_hR : Chain (sb' L) R)
    (h : ∃ l' u', trans l' u u' ∧ (∀ side, R side t u') ∧ L .tau l') :
    sb' L R true (.step t) u :=
  ⟨fun _ => step_ss'_step_l h, nofun⟩

theorem step_sb'_true_brS_l (hR : Chain (sb' L) R) {c : C.I} {k : C.O c → CTree E C X}
    (h : ∀ x, ∃ l' u', trans l' u u' ∧ (∀ side, R side (k x) u') ∧ L .tau l') :
    sb' L R true (.brS c k) u :=
  step_sb'_true_br_l hR fun x => b_chain hR true _ _ (step_sb'_true_step_l hR (h x))

end ProofRules

/-! ## Inversion rules -/

section InversionRules
variable {L : Label E → Label F → Prop} {R : Rel3 Bool (CTree E C X) (CTree F D Y)}
  {t : CTree E C X} {u : CTree F D Y}

theorem sb'_true_vis_inv {e : E.I} {f : F.I} {k : E.O e → CTree E C X}
    {k' : F.O f → CTree F D Y} (h : sb' L R true (.vis e k) (.vis f k')) (x : E.O e) :
    ∃ y, (∀ side, R side (k x) (k' y)) ∧ L (.obs e x) (.obs f y) := by
  obtain ⟨l', u', hu, hr, hl⟩ := ss'_vis_l_inv x (h.1 rfl)
  obtain ⟨y, rfl, rfl⟩ := trans_vis_inv hu
  exact ⟨y, hr, hl⟩

theorem sb'_true_vis_l_inv {e : E.I} {k : E.O e → CTree E C X} (x : E.O e)
    (h : sb' L R true (.vis e k) u) :
    ∃ l' u', trans l' u u' ∧ (∀ side, R side (k x) u') ∧ L (.obs e x) l' :=
  ss'_vis_l_inv x (h.1 rfl)

/-- Rocq `sb'_eq_vis_invT` concludes equality of the answer types; in Lean the events themselves
are equal. -/
theorem sb'_eq_vis_invT {R : Rel3 Bool (CTree E C X) (CTree E D Y)} {side : Bool} {e f : E.I}
    {k : E.O e → CTree E C X} {k' : E.O f → CTree E D Y} (h : sb' Eq R side (.vis e k) (.vis f k'))
    (x : E.O e) (x' : E.O f) : e = f := by
  cases side
  · obtain ⟨_, _, hu, -, rfl⟩ := ss'_vis_l_inv x' (h.2 rfl)
    obtain ⟨_, -, hl⟩ := trans_vis_inv hu
    exact (obs_eq_inv hl).1.symm
  · obtain ⟨_, _, hu, -, rfl⟩ := ss'_vis_l_inv x (h.1 rfl)
    obtain ⟨_, -, hl⟩ := trans_vis_inv hu
    exact (obs_eq_inv hl).1

theorem sb'_eq_vis_inv {R : Rel3 Bool (CTree E C X) (CTree E D Y)} {side : Bool} {e : E.I}
    {k : E.O e → CTree E C X} {k' : E.O e → CTree E D Y} (h : sb' Eq R side (.vis e k) (.vis e k'))
    (x : E.O e) : ∀ s, R s (k x) (k' x) := by
  cases side
  · obtain ⟨_, _, hu, hr, rfl⟩ := ss'_vis_l_inv x (h.2 rfl)
    obtain ⟨y, rfl, hl⟩ := trans_vis_inv hu
    cases eq_of_heq (obs_eq_inv hl).2
    exact hr
  · obtain ⟨_, _, hu, hr, rfl⟩ := ss'_vis_l_inv x (h.1 rfl)
    obtain ⟨y, rfl, hl⟩ := trans_vis_inv hu
    cases eq_of_heq (obs_eq_inv hl).2
    exact hr

theorem sb'_true_vis_l_inv' [RespectsVal L] [RespectsTau L] {e : E.I} {k : E.O e → CTree E C X}
    (h : sb' L R true (.vis e k) u) (x : E.O e) :
    ∃ (f : F.I) (k' : F.O f → CTree F D Y) (y : F.O f),
      Epsilon u (.vis f k') ∧ L (.obs e x) (.obs f y) ∧ ∀ side, R side (k x) (k' y) := by
  obtain ⟨l', u'', hu, hs, hl⟩ := ss'_vis_l_inv x (h.1 rfl)
  obtain ⟨u', h₁, h₂, h₃⟩ := trans_epsilon hu
  cases h₂ with
  | ret =>
    obtain ⟨-, rfl⟩ := trans_ret_inv h₃
    exact absurd ((RespectsVal.respects_val _ _ hl).2 (.val _)) isVal_obs
  | vis f k' =>
    obtain ⟨y, rfl, rfl⟩ := trans_vis_inv h₃
    exact ⟨f, k', y, h₁, hl, hs⟩
  | step =>
    obtain ⟨-, rfl⟩ := trans_step_inv h₃
    cases (RespectsTau.respects_tau _ _ hl).2 rfl

theorem sb'_true_br_l_inv {c : C.I} {k : C.O c → CTree E C X} (h : sb' L R true (.br c k) u)
    (x : C.O c) : ∃ u', Epsilon u u' ∧ R true (k x) u' :=
  ss'_gen_br (h.1 rfl) x

theorem sb'_false_br_l_inv {c : D.I} {k : D.O c → CTree F D Y} (h : sb' L R false t (.br c k))
    (x : D.O c) : ∃ t', Epsilon t t' ∧ R false t' (k x) :=
  ss'_gen_br (h.2 rfl) x

theorem sb'_true_guard_l_inv (h : sb' L R true (.guard t) u) :
    ∃ u', Epsilon u u' ∧ R true t u' :=
  ss'_gen_guard (h.1 rfl)

theorem sb'_false_guard_l_inv (h : sb' L R false t (.guard u)) :
    ∃ t', Epsilon t t' ∧ R false t' u :=
  ss'_gen_guard (h.2 rfl)

theorem sbisim'_br_l_inv {c : C.I} (x : C.O c) {k : C.O c → CTree E C X}
    (h : gfp (sb' L) true (.br c k) u) : gfp (sb' L) true (k x) u := by
  obtain ⟨u', he, hr⟩ := sb'_true_br_l_inv (gfp_sb'_unfold.1 h) x
  exact gfp_sb'_unfold.2 ⟨fun _ => step_ss'_epsilon_r ((gfp_sb'_unfold.1 hr).1 rfl) he, nofun⟩

theorem sbisim'_br_r_inv {c : D.I} (x : D.O c) {k : D.O c → CTree F D Y}
    (h : gfp (sb' L) false t (.br c k)) : gfp (sb' L) false t (k x) := by
  obtain ⟨t', he, hr⟩ := sb'_false_br_l_inv (gfp_sb'_unfold.1 h) x
  exact gfp_sb'_unfold.2 ⟨nofun, fun _ => step_ss'_epsilon_r ((gfp_sb'_unfold.1 hr).2 rfl) he⟩

theorem sbisim'_guard_l_inv (h : gfp (sb' L) true (.guard t) u) : gfp (sb' L) true t u := by
  obtain ⟨u', he, hr⟩ := sb'_true_guard_l_inv (gfp_sb'_unfold.1 h)
  exact gfp_sb'_unfold.2 ⟨fun _ => step_ss'_epsilon_r ((gfp_sb'_unfold.1 hr).1 rfl) he, nofun⟩

theorem sbisim'_guard_r_inv (h : gfp (sb' L) false t (.guard u)) : gfp (sb' L) false t u := by
  obtain ⟨t', he, hr⟩ := sb'_false_guard_l_inv (gfp_sb'_unfold.1 h)
  exact gfp_sb'_unfold.2 ⟨nofun, fun _ => step_ss'_epsilon_r ((gfp_sb'_unfold.1 hr).2 rfl) he⟩

end InversionRules

/-! ## Up-to principles -/

/-- `R` holds below a `guard`. -/
def guard_ctx (R : Pred (CTree E C X)) (t : CTree E C X) : Prop := ∃ t', t = .guard t' ∧ R t'

/-- `R` holds of `k0 x` for every value `x` satisfying `P` that `t0` can return, where
`t = t0 >>= k0` and `t0` only performs value transitions. -/
def pure_bind_ctx {X0 : Type u} (P : X0 → Prop) (R : Pred (CTree E C X)) (t : CTree E C X) :
    Prop :=
  ∃ (t0 : CTree E C X0) (k0 : X0 → CTree E C X), t = t0 >>= k0 ∧
    (∀ l t', trans l t0 t' → ∃ v, l = .val v ∧ P v) ∧ ∀ x, P x → R (k0 x)

section Upto
variable (L : Label E → Label F → Prop)

/-- Up-to `ss` on the left. -/
def ss_ctx3_l : Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R b t u := b = true ∧ ss L (fun t u => ∀ side, R side t u) t u
  mono h _ t u H := ⟨H.1, (ss L).mono (fun _ _ h' s => h s _ _ (h' s)) t u H.2⟩

/-- Up-to `guard` on the left. -/
def guard_ctx3_l : Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R b t u := guard_ctx (fun t => R b t u) t
  mono h b _ u H := let ⟨t', e, r⟩ := H; ⟨t', e, h b t' u r⟩

/-- Up-to `guard` on the right. -/
def guard_ctx3_r : Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R b t u := guard_ctx (fun u => R b t u) u
  mono h b t _ H := let ⟨u', e, r⟩ := H; ⟨u', e, h b t u' r⟩

/-- Up-to `EpsilonDet` on the left (side `true` only). -/
def epsilon_det_ctx3_l : Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R b t u := b = true ∧ epsilon_det_ctx (fun t => R b t u) t
  mono h b _ u H := let ⟨hb, t', e, r⟩ := H; ⟨hb, t', e, h b t' u r⟩

/-- Up-to a pure prefix on the left (side `true` only). -/
def pure_bind_ctx3_l {X0 : Type u} (P : X0 → Prop) :
    Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R b t u := b = true ∧ pure_bind_ctx P (fun t => R b t u) t
  mono h b _ u H :=
    let ⟨hb, t0, k0, e, htr, hk⟩ := H
    ⟨hb, t0, k0, e, htr, fun x hx => h b _ u (hk x hx)⟩

/-- Up-to `Epsilon` on the right (side `true` only). -/
def epsilon_ctx3_r : Mon (Rel3 Bool (CTree E C X) (CTree F D Y)) where
  body R b t u := b = true ∧ epsilon_ctx (fun u => R b t u) u
  mono h b t _ H := let ⟨hb, u', e, r⟩ := H; ⟨hb, u', e, h b t u' r⟩

variable {L} {R : Rel3 Bool (CTree E C X) (CTree F D Y)}

theorem ss_st'_l (hR : Chain (sb' L) R) : ∀ side t u, ss_ctx3_l L R side t u → R side t u := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X) (CTree F D Y) =>
    ∀ side t u, ss_ctx3_l L R side t u → R side t u) ?_ ?_ R hR
  · intro T hT s t u ⟨hs, hss⟩
    exact Rel3.inf_apply.2 fun R hR => hT R hR s t u
      ⟨hs, (ss L).mono (fun _ _ h s => Rel3.inf_apply.1 (h s) R hR) t u hss⟩
  · intro R hR ih side t u ⟨hs, hss⟩
    subst hs
    have hss' := (ss L).mono (fun _ _ h s => b_chain hR s _ _ (h s)) t u hss
    refine sb'_true_ss'.2 ⟨fun _ l t' ht => ?_, fun c k hk x => ?_, fun t' ht => ?_⟩
    · obtain ⟨l', u', h₁, h₂, h₃⟩ := hss l t' ht
      exact ⟨l', u', h₁, fun s => b_chain hR s _ _ (h₂ s), h₃⟩
    · subst hk; exact ⟨u, .refl _, ih true _ _ ⟨rfl, ss_br_l_inv hss' x⟩⟩
    · subst ht; exact ⟨u, .refl _, ih true _ _ ⟨rfl, ss_guard_l_inv hss'⟩⟩

theorem guard_ctx3_l_sbisim' (hR : Chain (sb' L) R) :
    ∀ side t u, guard_ctx3_l R side t u → R side t u := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X) (CTree F D Y) =>
    ∀ side t u, guard_ctx3_l R side t u → R side t u) ?_ ?_ R hR
  · intro T hT s t u ⟨t', e, r⟩
    exact Rel3.inf_apply.2 fun R hR => hT R hR s t u ⟨t', e, Rel3.inf_apply.1 r R hR⟩
  · intro R hR _ side t u ⟨t', e, r⟩
    subst e; exact step_sb'_guard_l hR r

theorem guard_ctx3_r_sbisim' (hR : Chain (sb' L) R) :
    ∀ side t u, guard_ctx3_r R side t u → R side t u := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X) (CTree F D Y) =>
    ∀ side t u, guard_ctx3_r R side t u → R side t u) ?_ ?_ R hR
  · intro T hT s t u ⟨u', e, r⟩
    exact Rel3.inf_apply.2 fun R hR => hT R hR s t u ⟨u', e, Rel3.inf_apply.1 r R hR⟩
  · intro R hR _ side t u ⟨u', e, r⟩
    subst e; exact step_sb'_guard_r hR r

theorem epsilon_det_ctx3_l_sbisim' (hR : Chain (sb' L) R) :
    ∀ side t u, epsilon_det_ctx3_l R side t u → R side t u := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X) (CTree F D Y) =>
    ∀ side t u, epsilon_det_ctx3_l R side t u → R side t u) ?_ ?_ R hR
  · intro T hT s t u ⟨hs, t', e, r⟩
    exact Rel3.inf_apply.2 fun R hR => hT R hR s t u ⟨hs, t', e, Rel3.inf_apply.1 r R hR⟩
  · intro R hR _ side t u ⟨hs, t', e, r⟩
    subst hs
    induction e with
    | refl => exact r
    | guard _ ih => exact step_sb'_guard_l hR (ih r)

theorem pure_bind_ctx3_l_sbisim' {X0 : Type u} (P : X0 → Prop) (hR : Chain (sb' L) R) :
    ∀ side t u, pure_bind_ctx3_l P R side t u → R side t u := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X) (CTree F D Y) =>
    ∀ side t u, pure_bind_ctx3_l P R side t u → R side t u) ?_ ?_ R hR
  · intro T hT s t u ⟨hs, t0, k0, e, htr, hk⟩
    exact Rel3.inf_apply.2 fun R hR => hT R hR s t u
      ⟨hs, t0, k0, e, htr, fun x hx => Rel3.inf_apply.1 (hk x hx) R hR⟩
  · intro R hR ih side t u ⟨hs, t0, k0, e, htr, hb⟩
    subst hs e
    refine sb'_true_ss'.2 ⟨fun hp l t' ht => ?_, fun c kk hk z => ?_, fun t' ht => ?_⟩
    · rcases trans_bind_inv ht with ⟨hl, t₁, ht₁, rfl⟩ | ⟨v, hv, hk⟩
      · obtain ⟨v, rfl, -⟩ := htr _ _ ht₁
        exact absurd (.val v) hl
      · obtain ⟨v', e, hPv⟩ := htr _ _ hv
        cases val_eq_inv e
        obtain rfl := productive_epsilon (productive_bind hp) (trans_val_epsilon hv).1
        exact ((hb v hPv).1 rfl).1 (by simpa using hp) l t' hk
    · rcases br_eq_bind_inv hk with ⟨v, rfl, hkv⟩ | ⟨k₁, rfl, hk₁⟩
      · obtain ⟨v', e, hPv⟩ := htr _ _ (trans_ret v)
        cases val_eq_inv e
        exact sb'_true_br_l_inv (hkv ▸ hb v hPv) z
      · refine ⟨u, .refl _, ih true _ _ ⟨rfl, k₁ z, k0, hk₁ z, fun l t' h => ?_,
          fun x hx => b_chain hR true _ _ (hb x hx)⟩⟩
        exact htr l t' (trans_br z h)
    · rcases guard_eq_bind_inv ht with ⟨v, rfl, hkv⟩ | ⟨t₁, rfl, hk₁⟩
      · obtain ⟨v', e, hPv⟩ := htr _ _ (trans_ret v)
        cases val_eq_inv e
        exact sb'_true_guard_l_inv (hkv ▸ hb v hPv)
      · exact ⟨u, .refl _, ih true _ _ ⟨rfl, t₁, k0, hk₁.symm,
          fun l t' h => htr l t' (trans_guard h), fun x hx => b_chain hR true _ _ (hb x hx)⟩⟩

theorem epsilon_ctx3_r_sbisim' (hR : Chain (sb' L) R) :
    ∀ side t u, epsilon_ctx3_r R side t u → R side t u := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X) (CTree F D Y) =>
    ∀ side t u, epsilon_ctx3_r R side t u → R side t u) ?_ ?_ R hR
  · intro T hT s t u ⟨hs, u', e, r⟩
    exact Rel3.inf_apply.2 fun R hR => hT R hR s t u ⟨hs, u', e, Rel3.inf_apply.1 r R hR⟩
  · intro R _ _ side t u ⟨hs, u', e, r⟩
    subst hs
    exact ⟨fun _ => step_ss'_epsilon_r (r.1 rfl) e, nofun⟩

/-- Chain elements are closed under `EpsilonDet` on both sides (side `true`). -/
theorem epsilon_det_st' (hR : Chain (sb' L) R) {t t' : CTree E C X} {u u' : CTree F D Y}
    (ht : EpsilonDet t t') (hu : EpsilonDet u u') (h : R true t' u') : R true t u :=
  epsilon_det_ctx3_l_sbisim' hR true t u ⟨rfl, t', ht,
    epsilon_ctx3_r_sbisim' hR true t' u ⟨rfl, u', epsilon_det_epsilon hu, h⟩⟩

theorem epsilon_det_sbt' (hR : Chain (sb' L) R) {t t' : CTree E C X} {u u' : CTree F D Y}
    (ht : EpsilonDet t t') (hu : EpsilonDet u u') (h : sb' L R true t' u') : sb' L R true t u :=
  epsilon_det_st' (.step hR) ht hu h

end Upto

/-! ## Up-to `bind` -/

section Bind
variable {L : Label E → Label F → Prop} {R0 : X → Y → Prop}

/-- Chain elements of `sb' L` are closed under `bind` (Rocq `bind_chain_gen`). -/
theorem sb'_chain_bind_gen {L0 : Label E → Label F → Prop} (hL0 : isUpdateValRel L R0 L0)
    {R : Rel3 Bool (CTree E C X') (CTree F D Y')} (hR : Chain (sb' L) R) :
    ∀ side (t : CTree E C X) (t' : CTree F D Y) (k : X → CTree E C X') (k' : Y → CTree F D Y'),
      gfp (sb' L0) side t t' → (∀ s x x', R0 x x' → R s (k x) (k' x')) →
      R side (t >>= k) (t' >>= k') := by
  refine tower (P := fun R : Rel3 Bool (CTree E C X') (CTree F D Y') => ∀ side t t' k k',
    gfp (sb' L0) side t t' → (∀ s x x', R0 x x' → R s (k x) (k' x')) →
    R side (t >>= k) (t' >>= k')) ?_ ?_ R hR
  · intro T hT side t t' k k' htt' hkk'
    exact Rel3.inf_apply.2 fun R hR =>
      hT R hR side t t' k k' htt' fun s x x' hx => Rel3.inf_apply.1 (hkk' s x x' hx) R hR
  · intro R hR ih side t t' k k' htt' hkk'
    have ih' := fun side t t' (h : gfp (sb' L0) side t t') =>
      ih side t t' k k' h fun s x x' hx => b_chain hR s _ _ (hkk' s x x' hx)
    refine ⟨fun hs => ?_, fun hs => ?_⟩ <;> subst hs
    · have tt := (gfp_sb'_unfold.1 htt').1 rfl
      have val_r : ∀ v : X, t = pure v → ∃ v', R0 v v' ∧ trans (.val v') t' .stuck := by
        rintro v rfl
        obtain ⟨l', u', hu', -, hll'⟩ := tt.1 (.ret v) _ _ (trans_ret v)
        obtain ⟨v₂, rfl, hv⟩ :=
          ((hL0 _ _ (wfVal_val v) (wfVal_trans hu')).2 hll').val_l
        cases trans_val_inv hu'
        exact ⟨v₂, hv, hu'⟩
      refine ⟨fun hp l u hu => ?_, fun c kk hk z => ?_, fun u hu => ?_⟩
      · rcases trans_bind_inv hu with ⟨hl, t₁, ht₁, rfl⟩ | ⟨x, hx, hk⟩
        · obtain ⟨l', t₁', ht₁', hss, hll'⟩ := tt.1 (productive_bind hp) l t₁ ht₁
          obtain ⟨hl', hL⟩ :=
            ((hL0 l l' (wfVal_trans ht₁) (wfVal_trans ht₁')).2 hll').nonval_l hl
          exact ⟨l', t₁' >>= k', trans_bind_l hl' ht₁', fun s => ih' s _ _ (hss s), hL⟩
        · obtain rfl := productive_epsilon (productive_bind hp) (trans_val_epsilon hx).1
          obtain ⟨x', hv, hu'⟩ := val_r x rfl
          obtain ⟨l'', u'', hu'', hss', hll''⟩ :=
            ((hkk' true x x' hv).1 rfl).1 (by simpa using hp) l u hk
          exact ⟨l'', u'', trans_bind_r hu' hu'', hss', hll''⟩
      · rcases br_eq_bind_inv hk with ⟨v, rfl, hkv⟩ | ⟨k₀, rfl, hk₀⟩
        · obtain ⟨v', hv, hu'⟩ := val_r v rfl
          obtain ⟨u', he, hr⟩ := ((hkk' true v v' hv).1 rfl).2.1 c kk hkv z
          exact ⟨u', epsilon_bind (trans_val_epsilon hu').1 he, hr⟩
        · exact ⟨t' >>= k', .refl _, by rw [hk₀ z]; exact ih' true _ _ (sbisim'_br_l_inv z htt')⟩
      · rcases guard_eq_bind_inv hu with ⟨v, rfl, hkv⟩ | ⟨t₀, rfl, hk₀⟩
        · obtain ⟨v', hv, hu'⟩ := val_r v rfl
          obtain ⟨u', he, hr⟩ := ((hkk' true v v' hv).1 rfl).2.2 u hkv
          exact ⟨u', epsilon_bind (trans_val_epsilon hu').1 he, hr⟩
        · exact ⟨t' >>= k', .refl _, hk₀ ▸ ih' true _ _ (sbisim'_guard_l_inv htt')⟩
    · have tt := (gfp_sb'_unfold.1 htt').2 rfl
      have val_l : ∀ v' : Y, t' = pure v' → ∃ v, R0 v v' ∧ trans (.val v) t .stuck := by
        rintro v' rfl
        obtain ⟨l', u', hu', -, hll'⟩ := tt.1 (.ret v') _ _ (trans_ret v')
        obtain ⟨v₁, rfl, hv⟩ :=
          ((hL0 _ _ (wfVal_trans hu') (wfVal_val v')).2 hll').val_r
        cases trans_val_inv hu'
        exact ⟨v₁, hv, hu'⟩
      refine ⟨fun hp l u hu => ?_, fun c kk hk z => ?_, fun u hu => ?_⟩
      · rcases trans_bind_inv hu with ⟨hl, t₁, ht₁, rfl⟩ | ⟨x, hx, hk⟩
        · obtain ⟨l', t₁', ht₁', hss, hll'⟩ := tt.1 (productive_bind hp) l t₁ ht₁
          obtain ⟨hl', hL⟩ :=
            ((hL0 l' l (wfVal_trans ht₁') (wfVal_trans ht₁)).2 hll').nonval_r hl
          exact ⟨l', t₁' >>= k, trans_bind_l hl' ht₁', fun s => ih' s _ _ (hss s), hL⟩
        · obtain rfl := productive_epsilon (productive_bind hp) (trans_val_epsilon hx).1
          obtain ⟨x', hv, hu'⟩ := val_l x rfl
          obtain ⟨l'', u'', hu'', hss', hll''⟩ :=
            ((hkk' false x' x hv).2 rfl).1 (by simpa using hp) l u hk
          exact ⟨l'', u'', trans_bind_r hu' hu'', hss', hll''⟩
      · rcases br_eq_bind_inv hk with ⟨v, rfl, hkv⟩ | ⟨k₀, rfl, hk₀⟩
        · obtain ⟨v', hv, hu'⟩ := val_l v rfl
          obtain ⟨u', he, hr⟩ := ((hkk' false v' v hv).2 rfl).2.1 c kk hkv z
          exact ⟨u', epsilon_bind (trans_val_epsilon hu').1 he, hr⟩
        · exact ⟨t >>= k, .refl _, by
            show R false _ _; rw [hk₀ z]; exact ih' false _ _ (sbisim'_br_r_inv z htt')⟩
      · rcases guard_eq_bind_inv hu with ⟨v, rfl, hkv⟩ | ⟨t₀, rfl, hk₀⟩
        · obtain ⟨v', hv, hu'⟩ := val_l v rfl
          obtain ⟨u', he, hr⟩ := ((hkk' false v' v hv).2 rfl).2.2 u hkv
          exact ⟨u', epsilon_bind (trans_val_epsilon hu').1 he, hr⟩
        · exact ⟨t >>= k, .refl _, by
            show R false _ _; rw [← hk₀]; exact ih' false _ _ (sbisim'_guard_r_inv htt')⟩

theorem st'_clo_bind {R : Rel3 Bool (CTree E C X') (CTree F D Y')} (hR : Chain (sb' L) R)
    {side : Bool} {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'}
    {k₂ : Y → CTree F D Y'} (h₁ : gfp (sb' (UpdateValRel L R0)) side t₁ t₂)
    (h₂ : ∀ x y, R0 x y → ∀ b, R b (k₁ x) (k₂ y)) : R side (t₁ >>= k₁) (t₂ >>= k₂) :=
  sb'_chain_bind_gen updateValRel_correct hR side _ _ _ _ h₁ fun b x y h => h₂ x y h b

theorem sbt'_clo_bind_gen {L0 : Label E → Label F → Prop} (hL0 : isUpdateValRel L R0 L0)
    {R : Rel3 Bool (CTree E C X') (CTree F D Y')} (hR : Chain (sb' L) R) {b : Bool}
    {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'} {k₂ : Y → CTree F D Y'}
    (h₁ : gfp (sb' L0) b t₁ t₂) (h₂ : ∀ x y, R0 x y → ∀ b, sb' L R b (k₁ x) (k₂ y)) :
    sb' L R b (t₁ >>= k₁) (t₂ >>= k₂) :=
  sb'_chain_bind_gen hL0 (.step hR) b _ _ _ _ h₁ fun b x y h => h₂ x y h b

theorem sbt'_clo_bind {R : Rel3 Bool (CTree E C X') (CTree F D Y')} (hR : Chain (sb' L) R)
    {b : Bool} {t₁ : CTree E C X} {t₂ : CTree F D Y} {k₁ : X → CTree E C X'}
    {k₂ : Y → CTree F D Y'} (h₁ : gfp (sb' (UpdateValRel L R0)) b t₁ t₂)
    (h₂ : ∀ x y, R0 x y → ∀ b, sb' L R b (k₁ x) (k₂ y)) : sb' L R b (t₁ >>= k₁) (t₂ >>= k₂) :=
  sbt'_clo_bind_gen updateValRel_correct hR h₁ h₂

end Bind

theorem st'_clo_bind_eq {R : Rel3 Bool (CTree E C X') (CTree E D X')} (hR : Chain (sb' Eq) R)
    {side : Bool} {t₁ : CTree E C X} {t₂ : CTree E D X} {k₁ : X → CTree E C X'}
    {k₂ : X → CTree E D X'} (h₁ : gfp (sb' Eq) side t₁ t₂) (h₂ : ∀ x b, R b (k₁ x) (k₂ x)) :
    R side (t₁ >>= k₁) (t₂ >>= k₂) :=
  sb'_chain_bind_gen (R0 := Eq) updateValRel_eq hR side _ _ _ _ h₁
    (by rintro b x _ rfl; exact h₂ x b)

theorem sbt'_clo_bind_eq {R : Rel3 Bool (CTree E C X') (CTree E D X')} (hR : Chain (sb' Eq) R)
    {b : Bool} {t₁ : CTree E C X} {t₂ : CTree E D X} {k₁ : X → CTree E C X'}
    {k₂ : X → CTree E D X'} (h₁ : gfp (sb' Eq) b t₁ t₂)
    (h₂ : ∀ x b, sb' Eq R b (k₁ x) (k₂ x)) : sb' Eq R b (t₁ >>= k₁) (t₂ >>= k₂) :=
  sbt'_clo_bind_gen (R0 := Eq) updateValRel_eq hR h₁ (by rintro x _ rfl b; exact h₂ x b)

/-! ## Derived rules and equivalence with `sbisim` -/

section Equiv
variable {L : Label E → Label F → Prop} {R : Rel3 Bool (CTree E C X) (CTree F D Y)}

theorem step_sb'_guard_l' (hR : Chain (sb' L) R) {t : CTree E C X} {u : CTree F D Y}
    (h : ∀ side, R side t u) : ∀ side, R side (.guard t) u :=
  fun side => guard_ctx3_l_sbisim' hR side _ _ ⟨t, rfl, h side⟩

theorem step_sb'_guard_r' (hR : Chain (sb' L) R) {t : CTree E C X} {u : CTree F D Y}
    (h : ∀ side, R side t u) : ∀ side, R side t (.guard u) :=
  fun side => guard_ctx3_r_sbisim' hR side _ _ ⟨u, rfl, h side⟩

theorem sbisim'_epsilon_l {t t' : CTree E C X} {u : CTree F D Y}
    (h : gfp (sb' L) true t u) (he : Epsilon t t') : gfp (sb' L) true t' u :=
  gfp_sb'_unfold.2 ⟨fun _ => ss'_gen_epsilon_l (fun _ _ h => (gfp_sb'_unfold.1 h).1 rfl)
    ((gfp_sb'_unfold.1 h).1 rfl) he, nofun⟩

theorem sbisim'_epsilon_r {t : CTree E C X} {u u' : CTree F D Y}
    (h : gfp (sb' L) false t u) (he : Epsilon u u') : gfp (sb' L) false t u' :=
  gfp_sb'_unfold.2 ⟨nofun, fun _ => ss'_gen_epsilon_l (fun _ _ h => (gfp_sb'_unfold.1 h).2 rfl)
    ((gfp_sb'_unfold.1 h).2 rfl) he⟩

theorem ss_sb'_l_chain (hR : Chain (sb' L) R) {t : CTree E C X} {u : CTree F D Y}
    (h : ss L (fun t u => ∀ b, R b t u) t u) : sb' L R true t u :=
  sb'_true_ss'.2 ⟨fun _ l t' ht => h l t' ht,
   fun _ _ hk x => by subst hk; exact ⟨u, .refl _, ss_st'_l hR true _ _ ⟨rfl, ss_br_l_inv h x⟩⟩,
   fun _ ht => by subst ht; exact ⟨u, .refl _, ss_st'_l hR true _ _ ⟨rfl, ss_guard_l_inv h⟩⟩⟩

theorem gfp_sb'_ss_sbisim {t : CTree E C X} {u : CTree F D Y} :
    (ss L (sbisim L) t u → gfp (sb' L) true t u) ∧
    (ss (flip L) (flip (sbisim L)) u t → gfp (sb' L) false t u) := by
  refine gfp_prop (b := sb' L) (P := fun R => ∀ t u, (ss L (sbisim L) t u → R true t u) ∧
    (ss (flip L) (flip (sbisim L)) u t → R false t u)) (tower ?_ ?_) t u
  · intro T hT t u
    exact ⟨fun h => Rel3.inf_apply.2 fun R hR => (hT R hR t u).1 h,
      fun h => Rel3.inf_apply.2 fun R hR => (hT R hR t u).2 h⟩
  · intro R hR ih t u
    have hs : ∀ t u, sbisim L t u → ∀ s, R s t u := fun t u h s => by
      cases s
      · exact (ih t u).2 (sbisim_unfold.1 h).2
      · exact (ih t u).1 (sbisim_unfold.1 h).1
    refine ⟨fun h => ss_sb'_l_chain hR ((ss L).mono (fun _ _ h => hs _ _ h) t u h),
      fun h => ⟨nofun, fun _ => ⟨fun _ l u' hu => ?_, fun c k hk x => ?_, fun u' hu => ?_⟩⟩⟩
    · obtain ⟨l', t', h₁, h₂, h₃⟩ := h l u' hu
      exact ⟨l', t', h₁, hs _ _ h₂, h₃⟩
    · subst hk; exact ⟨t, .refl _, (ih t (k x)).2 (ss_br_l_inv h x)⟩
    · subst hu; exact ⟨t, .refl _, (ih t u').2 (ss_guard_l_inv h)⟩

theorem gfp_sb'_true_ss_sbisim {t : CTree E C X} {u : CTree F D Y}
    (h : ss L (sbisim L) t u) : gfp (sb' L) true t u :=
  gfp_sb'_ss_sbisim.1 h

/-- The alternative bisimulation `sbisim'` is equivalent to `sbisim`. -/
theorem sbisim_sbisim' {t : CTree E C X} {t' : CTree F D Y} : sbisim L t t' ↔ sbisim' L t t' :=
  ⟨fun h side => by
    cases side
    · exact gfp_sb'_ss_sbisim.2 (sbisim_unfold.1 h).2
    · exact gfp_sb'_ss_sbisim.1 (sbisim_unfold.1 h).1,
   fun h => le_gfp (b := sb L) (x := sbisim' L) (fun t u h =>
      ⟨fun l t₁ ht => by
        obtain ⟨t₀, he, hp, ht₀⟩ := trans_epsilon ht
        exact ((gfp_sb'_unfold.1 (sbisim'_epsilon_l (h true) he)).1 rfl).1 hp l t₁ ht₀,
       fun l u₁ hu => by
        obtain ⟨u₀, he, hp, hu₀⟩ := trans_epsilon hu
        exact ((gfp_sb'_unfold.1 (sbisim'_epsilon_r (h false) he)).2 rfl).1 hp l u₁ hu₀⟩)
      t t' h⟩

theorem sbisim_gfp_sb' {side : Bool} {t : CTree E C X} {t' : CTree F D Y} (h : sbisim L t t') :
    gfp (sb' L) side t t' :=
  sbisim_sbisim'.1 h side

theorem ss_sbisim_gfp_sb' {t : CTree E C X} {u : CTree F D Y} :
    (gfp (sb' L) true t u → ss L (sbisim L) t u) ∧
    (gfp (sb' L) false t u → ss (flip L) (flip (sbisim L)) u t) :=
  ⟨fun h l t₁ ht => by
    obtain ⟨t₀, he, hp, ht₀⟩ := trans_epsilon ht
    obtain ⟨l', u', h₁, h₂, h₃⟩ :=
      ((gfp_sb'_unfold.1 (sbisim'_epsilon_l h he)).1 rfl).1 hp l t₁ ht₀
    exact ⟨l', u', h₁, sbisim_sbisim'.2 h₂, h₃⟩,
   fun h l u₁ hu => by
    obtain ⟨u₀, he, hp, hu₀⟩ := trans_epsilon hu
    obtain ⟨l', t', h₁, h₂, h₃⟩ :=
      ((gfp_sb'_unfold.1 (sbisim'_epsilon_r h he)).2 rfl).1 hp l u₁ hu₀
    exact ⟨l', t', h₁, sbisim_sbisim'.2 h₂, h₃⟩⟩

end Equiv

end CTree
