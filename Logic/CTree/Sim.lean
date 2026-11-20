/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Trans
public import Logic.Simulation
public import Logic.Setoid
public import Logic.Events.Writer

/-!
# Conditional simulation of ctrees

`csim ER RV` simulates every source transition forward and, only from a source that can transition,
every target transition backward; it is a shallow Kripke simulation in the sense of
`Logic/Simulation.lean`, so it transports TICL formulas along `framer` (`ticl_csim`). Also the
`Framable` trees (admissible events, guarded hidden branches) and the structural proof principle
`csim_structural` (← `CTree/Logic/Sim.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinduction
open ITree (Effect)

section ConditionalSimulation
variable {E B : Effect.{u}} {X : Type u}

/-- Labels preserve responses (`HEq`); observations follow `ER` and returns `RV`. -/
inductive simL (ER : event_rel E) (RV : X → X → Prop) : Label E → Label E → Prop
  | tau : simL ER RV .tau .tau
  | obs (e e' : E.I) (v : E.O e) (v' : E.O e') :
      ER e e' → HEq v v' → simL ER RV (.obs e v) (.obs e' v')
  | val (x x' : X) : RV x x' → simL ER RV (.val x) (.val x')

/-- A tree can make an LTS transition. -/
def can_trans (t : CTree E B X) : Prop := ∃ l t', trans l t t'

/-- Conditional LTS simulation: forward always, backward only from a tree that can transition. -/
def csimF (ER : event_rel E) (RV : X → X → Prop) : Mon (Rel (CTree E B X) (CTree E B X)) where
  body R t t' :=
    (∀ l t1, trans l t t1 → ∃ l' t1', trans l' t' t1' ∧ simL ER RV l l' ∧ R t1 t1') ∧
    (can_trans t → ∀ l' t1', trans l' t' t1' →
      ∃ l t1, trans l t t1 ∧ simL ER RV l l' ∧ R t1 t1')
  mono h _ _ H :=
    ⟨fun l t1 ht => let ⟨l', t1', ht', hl, hr⟩ := H.1 l t1 ht; ⟨l', t1', ht', hl, h _ _ hr⟩,
     fun hc l' t1' ht' =>
      let ⟨l, t1, ht, hl, hr⟩ := H.2 hc l' t1' ht'; ⟨l, t1, ht, hl, h _ _ hr⟩⟩

/-- Greatest fixed point of conditional simulation, matching the hypotheses of `ticl_sim`. -/
def csim (ER : event_rel E) (RV : X → X → Prop) : Rel (CTree E B X) (CTree E B X) :=
  gfp (csimF ER RV)

/-- A stuck source conditionally simulates every target. -/
theorem csim_stuck_l (ER : event_rel E) (RV : X → X → Prop) {R : Rel (CTree E B X) (CTree E B X)}
    (hR : Chain (csimF ER RV) R) (t' : CTree E B X) : R .stuck t' :=
  b_chain hR _ _ ⟨fun _ _ ht => (trans_stuck_inv ht).elim,
    fun ⟨_, _, ht⟩ => (trans_stuck_inv ht).elim⟩

/-- Leading silent guards preserve transition availability. -/
theorem can_trans_guard (t : CTree E B X) : can_trans (.guard t) ↔ can_trans t :=
  ⟨fun ⟨l, u, ht⟩ => ⟨l, u, trans_guard_inv ht⟩, fun ⟨l, u, ht⟩ => ⟨l, u, trans_guard ht⟩⟩

/-- Forward matching starts from a related, not necessarily equal, world. -/
theorem csim_ktrans_l (ER : event_rel E) (RV : X → X → Prop) (t t' : CTree E B X)
    (w w' : World E) (u : CTree E B X) (z : World E) (hS : csim ER RV t t')
    (hW : simW ER RV w w') (hT : ktrans t w u z) :
    ∃ u' z', ktrans t' w' u' z' ∧ csim ER RV u u' ∧ simW ER RV z z' := by
  have hnd' := (simW_not_done_iff ER RV hW).1 (Kripke.ktrans_not_done hT)
  have hf := (gfp_pfp (b := csimF ER RV) t t' hS).1
  cases hT with
  | tau _ htr =>
    obtain ⟨l', u', ht', hL, hR⟩ := hf _ _ htr
    cases hL; exact ⟨u', w', .tau hnd' ht', hR, hW⟩
  | obs e v _ htr =>
    obtain ⟨l', u', ht', hL, hR⟩ := hf _ _ htr
    cases hL with
    | obs _ e' _ v' he hv => exact ⟨u', .obs e' v', .obs e' v' hnd' ht', hR, .obs e e' v v' he hv⟩
  | done x htr =>
    obtain ⟨l', u', ht', hL, hR⟩ := hf _ _ htr
    cases hL with
    | val _ x' hx => cases hW; exact ⟨u', .done x', .done x' ht', hR, .done x x' hx⟩
  | finish e v x htr =>
    obtain ⟨l', u', ht', hL, hR⟩ := hf _ _ htr
    cases hL with
    | val _ x' hx =>
      cases hW with
      | obs _ e' _ v' he hv =>
        exact ⟨u', .finish e' v' x', .finish e' v' x' ht', hR, .finish e e' v v' x x' he hv hx⟩

/-- Backward matching remains conditional on source progress. -/
theorem csim_ktrans_r (ER : event_rel E) (RV : X → X → Prop) (t t' : CTree E B X)
    (w w' : World E) (u' : CTree E B X) (z' : World E) (hS : csim ER RV t t')
    (hW : simW ER RV w w') (hc : can_step t w) (hT : ktrans t' w' u' z') :
    ∃ u z, ktrans t w u z ∧ csim ER RV u u' ∧ simW ER RV z z' := by
  have hnd := can_step_not_done hc
  obtain ⟨v, _, hc⟩ := hc
  have hC : can_trans t := let ⟨l, ht, _⟩ := ktrans_trans.1 hc; ⟨l, v, ht⟩
  have hb := (gfp_pfp (b := csimF ER RV) t t' hS).2 hC
  cases hT with
  | tau _ htr =>
    obtain ⟨l, u, ht, hL, hR⟩ := hb _ _ htr
    cases hL; exact ⟨u, w, .tau hnd ht, hR, hW⟩
  | obs e' v' _ htr =>
    obtain ⟨l, u, ht, hL, hR⟩ := hb _ _ htr
    cases hL with
    | obs e _ v _ he hv => exact ⟨u, .obs e v, .obs e v hnd ht, hR, .obs e e' v v' he hv⟩
  | done x' htr =>
    obtain ⟨l, u, ht, hL, hR⟩ := hb _ _ htr
    cases hL with
    | val x _ hx => cases hW; exact ⟨u, .done x, .done x ht, hR, .done x x' hx⟩
  | finish e' v' x' htr =>
    obtain ⟨l, u, ht, hL, hR⟩ := hb _ _ htr
    cases hL with
    | val x _ hx =>
      cases hW with
      | obs e _ v _ he hv =>
        exact ⟨u, .finish e v x, .finish e v x ht, hR, .finish e e' v v' x x' he hv hx⟩

/-- Conditional simulation transports every formula along `framer`. -/
theorem ticl_csim (b : Bool) (ER : event_rel E) (RV : X → X → Prop) (p : TiclAt E X b)
    (hu : sim_unique b ER RV) (t t' : CTree E B X) (w w' : World E) (hS : csim ER RV t t')
    (hW : simW ER RV w w') (h : entails p t w) : entails (framer X b ER RV p) t' w' :=
  ticl_sim (M := CTree) ER RV (csim ER RV) (csim_ktrans_l ER RV) (csim_ktrans_r ER RV) b p hu
    t t' w w' hS hW h

end ConditionalSimulation

/-- Unconditional bisimulation supplies both conditional simulation matches. -/
theorem sbisim_csim {E B : Effect.{u}} {X : Type u} (ER : event_rel E) (RV : X → X → Prop)
    (t u : CTree E B X) : sbisim (simL ER RV) t u → csim ER RV t u := by
  refine gfp_prop (b := csimF ER RV) (P := fun R => ∀ t u, sbisim (simL ER RV) t u → R t u)
    (tower (fun T hT t u h => Rel.inf_apply.2 fun R hR => hT R hR t u h) ?_) t u
  intro R _ IH t u h
  obtain ⟨hf, hb⟩ := sbisim_unfold.1 h
  refine ⟨fun l t' ht => ?_, fun _ l' u' hu => ?_⟩
  · obtain ⟨l', u', hu, hR, hL⟩ := hf l t' ht; exact ⟨l', u', hu, hL, IH _ _ hR⟩
  · obtain ⟨l, t', ht, hR, hL⟩ := hb l' u' hu; exact ⟨l, t', ht, hL, IH _ _ hR⟩

section GuardsToStep
variable {E B : Effect.{u}} {X Y : Type u}

/-- A finite chain of `guard`s ending in a visible `step`: a hidden branch visible to `trans`. -/
inductive guards_to_step : CTree E B X → Prop
  | step (t u : CTree E B X) : t.unfold = .step u → guards_to_step t
  | guard (t u : CTree E B X) : t.unfold = .guard u → guards_to_step u → guards_to_step t

/-- A guarded-step prefix can transition. -/
theorem guards_to_step_can_trans (t : CTree E B X) (h : guards_to_step t) : can_trans t := by
  induction h with
  | step t u H => exact ⟨.tau, u, show Trans_ _ t.unfold _ by rw [H]; exact .step⟩
  | guard t u H _ ih =>
    obtain ⟨l, v, ht⟩ := ih
    exact ⟨l, v, show Trans_ _ t.unfold _ by rw [H]; exact .guard ht⟩

/-- A leading guard preserves a guarded-step prefix. -/
theorem guards_to_step_guard (t : CTree E B X) (h : guards_to_step t) :
    guards_to_step (.guard t) :=
  .guard _ t (unfold_guard t) h

/-- Binding preserves a guarded-step prefix. -/
theorem guards_to_step_bind (t : CTree E B X) (k : X → CTree E B Y) (h : guards_to_step t) :
    guards_to_step (t >>= k) := by
  induction h with
  | step t u H => exact .step _ (u >>= k) (by rw [unfold_bind, H])
  | guard t u H _ ih => exact .guard _ (u >>= k) (by rw [unfold_bind, H]) ih

end GuardsToStep

section Framable
variable {E B : Effect.{u}} (okE : E.I → Prop)

/-- One framable node: events satisfy `okE` and hidden children are guarded-step prefixes. -/
inductive framableF {A : Type u} (R : CTree E B A → Prop) : CTreeF E B A (CTree E B A) → Prop
  | ret (x : A) : framableF R (.ret x)
  | stuck : framableF R .stuck
  | step (t : CTree E B A) : R t → framableF R (.step t)
  | guard (t : CTree E B A) : R t → framableF R (.guard t)
  | vis (e : E.I) (k : E.O e → CTree E B A) : okE e → (∀ x, R (k x)) → framableF R (.vis e k)
  | br (c : B.I) (k : B.O c → CTree E B A) : (∀ y, guards_to_step (k y)) → (∀ y, R (k y)) →
      framableF R (.br c k)

/-- `framableF` is monotone in the continuation predicate. -/
theorem framableF_mono {A : Type u} {R S : CTree E B A → Prop} (h : ∀ t, R t → S t)
    {ot : CTreeF E B A (CTree E B A)} (H : framableF okE R ot) : framableF okE S ot := by
  cases H with
  | ret x => exact .ret x
  | stuck => exact .stuck
  | step t ht => exact .step t (h _ ht)
  | guard t ht => exact .guard t (h _ ht)
  | vis e k he hk => exact .vis e k he fun x => h _ (hk x)
  | br c k hg hk => exact .br c k hg fun y => h _ (hk y)

/-- Monotone observation operator for framability. -/
def fframable {A : Type u} : Mon (Pred (CTree E B A)) where
  body R t := framableF okE R t.unfold
  mono h _ H := framableF_mono okE h H

/-- Trees with admissible events and guarded hidden branches; closed under bind and iteration. -/
def Framable {A : Type u} : CTree E B A → Prop := gfp (fframable okE)

/-- Expose exactly one framable node. -/
theorem framable_unfold {A : Type u} (t : CTree E B A) :
    Framable okE t ↔ framableF okE (Framable okE) t.unfold :=
  ⟨fun h => gfp_pfp (b := fframable okE) t h, fun h => b_chain (gfp_chain (fframable okE)) t h⟩

/-- Returns are framable. -/
theorem fr_ret {A : Type u} (x : A) : Framable okE (pure x : CTree E B A) :=
  (framable_unfold okE _).2 (by rw [unfold_pure]; exact .ret x)

/-- Stuck trees are framable. -/
theorem fr_stuck {A : Type u} : Framable okE (.stuck : CTree E B A) :=
  (framable_unfold okE _).2 (by rw [unfold_stuck]; exact .stuck)

/-- A leading guard preserves framability. -/
theorem fr_guard {A : Type u} (t : CTree E B A) (h : Framable okE t) : Framable okE (.guard t) :=
  (framable_unfold okE _).2 (by rw [unfold_guard]; exact .guard t h)

/-- An admissible event with framable continuations is framable. -/
theorem fr_vis {A : Type u} (e : E.I) (k : E.O e → CTree E B A) (he : okE e)
    (hk : ∀ x, Framable okE (k x)) : Framable okE (.vis e k) :=
  (framable_unfold okE _).2 (by rw [unfold_vis]; exact .vis e k he hk)

/-- Bind preserves framability into every chain stage. -/
theorem framable_bind_chain {X A : Type u} {R : Pred (CTree E B A)}
    (hR : Chain (fframable okE) R) :
    ∀ (t : CTree E B X) (k : X → CTree E B A), Framable okE t → (∀ x, R (k x)) → R (t >>= k) := by
  refine tower (P := fun R : Pred (CTree E B A) =>
    ∀ (t : CTree E B X) (k : X → CTree E B A), Framable okE t → (∀ x, R (k x)) → R (t >>= k))
    (fun T hT t k ht hk => Pred.inf_apply.2 fun R hR =>
      hT R hR t k ht fun x => Pred.inf_apply.1 (hk x) R hR) ?_ R hR
  intro R hR IH t k ht hk
  have hk' : ∀ x, R (k x) := fun x => b_chain hR _ (hk x)
  show framableF okE R (t >>= k).unfold
  rw [unfold_bind]
  have ht := (framable_unfold okE t).1 ht
  generalize t.unfold = ot at ht ⊢
  cases ht with
  | ret x => exact hk x
  | stuck => exact .stuck
  | step t ht => exact .step _ (IH t k ht hk')
  | guard t ht => exact .guard _ (IH t k ht hk')
  | vis e k' he hk'' => exact .vis e _ he fun x => IH _ k (hk'' x) hk'
  | br c k' hg hk'' =>
    exact .br c _ (fun y => guards_to_step_bind _ k (hg y)) fun y => IH _ k (hk'' y) hk'

/-- Bind preserves framability. -/
theorem framable_bind {X A : Type u} (t : CTree E B X) (k : X → CTree E B A)
    (ht : Framable okE t) (hk : ∀ x, Framable okE (k x)) : Framable okE (t >>= k) :=
  framable_bind_chain okE (gfp_chain _) t k ht hk

/-- Iteration of framable bodies is framable. -/
theorem framable_iter {I A : Type u} (body : I → CTree E B (I ⊕ A))
    (h : ∀ i, Framable okE (body i)) : ∀ i, Framable okE (CTree.iter body i) := by
    coinduction R hR IH
    intro i
    rw [unfold_iter]
    refine framable_bind_chain okE (.step hR) (body i) _ (h i) ?_
    rintro (i' | a)
    · show framableF okE R (CTree.guard _).unfold
      rw [unfold_guard]; exact .guard _ (IH i')
    · show framableF okE R (pure a : CTree E B A).unfold
      rw [unfold_pure]; exact .ret a

end Framable

/-- One-node simulation shape up to `S`, avoiding coinduction through silent guards. Related
events have the same answer type; their continuations are related on `HEq` answers. -/
inductive csim_shape {E B : Effect.{u}} {X : Type u} (ER : event_rel E) (RV : X → X → Prop)
    (S : CTree E B X → CTree E B X → Prop) :
    CTreeF E B X (CTree E B X) → CTreeF E B X (CTree E B X) → Prop
  | stuck (v : CTreeF E B X (CTree E B X)) : csim_shape ER RV S .stuck v
  | ret (x x' : X) : RV x x' → csim_shape ER RV S (.ret x) (.ret x')
  | step (t t' : CTree E B X) : S t t' → csim_shape ER RV S (.step t) (.step t')
  | guard (t t' : CTree E B X) : S t t' → csim_shape ER RV S (.guard t) (.guard t')
  | vis (e e' : E.I) (k : E.O e → CTree E B X) (k' : E.O e' → CTree E B X) :
      ER e e' → E.O e = E.O e' → (∀ y y', HEq y y' → S (k y) (k' y')) →
      csim_shape ER RV S (.vis e k) (.vis e' k')
  | br (c : B.I) (k k' : B.O c → CTree E B X) :
      (∀ y, can_trans (k y)) → (∀ y, S (k y) (k' y)) → csim_shape ER RV S (.br c k) (.br c k')

section StructuralSimulation
variable {E B : Effect.{u}} {X : Type u} (ER : event_rel E) (RV : X → X → Prop)
  (S : CTree E B X → CTree E B X → Prop)
  (Hshape : ∀ t t', S t t' → csim_shape ER RV S t.unfold t'.unfold)
include Hshape

/-- Structural matching transports a transition forward by finite induction on `Trans_`. -/
theorem csim_shape_trans_l {R : Rel (CTree E B X) (CTree E B X)} (hR : Chain (csimF ER RV) R)
    (HS : ∀ t t', S t t' → R t t') :
    ∀ l ot (u : CTree E B X), Trans_ l ot u → ∀ ot', csim_shape ER RV S ot ot' →
      ∃ l' u', Trans_ l' ot' u' ∧ simL ER RV l l' ∧ R u u' := by
  intro l ot u ht
  induction ht with
  | br x _ ih =>
    intro ot' hsh
    cases hsh with
    | br _ _ k' _ hS =>
      obtain ⟨l', u', ht', hL, hR'⟩ := ih _ (Hshape _ _ (hS x))
      exact ⟨l', u', .br x ht', hL, hR'⟩
  | guard _ ih =>
    intro ot' hsh
    cases hsh with
    | guard _ t' hS =>
      obtain ⟨l', u', ht', hL, hR'⟩ := ih _ (Hshape _ _ hS)
      exact ⟨l', u', .guard ht', hL, hR'⟩
  | step =>
    intro ot' hsh
    cases hsh with
    | step _ t' hS => exact ⟨.tau, t', .step, .tau, HS _ _ hS⟩
  | obs x =>
    intro ot' hsh
    cases hsh with
    | vis _ e' _ k' he hY hk =>
      exact ⟨.obs e' (cast hY x), k' (cast hY x), .obs _, .obs _ _ _ _ he (cast_heq hY x).symm,
        HS _ _ (hk _ _ (cast_heq hY x).symm)⟩
  | val =>
    intro ot' hsh
    cases hsh with
    | ret _ x' hx => exact ⟨.val x', .stuck, .val, .val _ _ hx, csim_stuck_l ER RV hR _⟩

/-- Structural matching transports a transition backward when the source can transition. -/
theorem csim_shape_trans_r {R : Rel (CTree E B X) (CTree E B X)} (hR : Chain (csimF ER RV) R)
    (HS : ∀ t t', S t t' → R t t') :
    ∀ l' ot' (u' : CTree E B X), Trans_ l' ot' u' → ∀ ot, csim_shape ER RV S ot ot' →
      can_trans (CTree.fold ot) → ∃ l u, Trans_ l ot u ∧ simL ER RV l l' ∧ R u u' := by
  have hstuck : ¬ can_trans (CTree.fold .stuck : CTree E B X) :=
    fun ⟨_, _, h⟩ => trans_stuck_inv h
  intro l' ot' u' ht
  induction ht with
  | br x _ ih =>
    intro ot hsh hc
    cases hsh with
    | stuck => exact (hstuck hc).elim
    | br _ k _ hcan hS =>
      obtain ⟨l, u, ht, hL, hR'⟩ :=
        ih _ (Hshape _ _ (hS x)) (by rw [fold_unfold]; exact hcan x)
      exact ⟨l, u, .br x ht, hL, hR'⟩
  | guard _ ih =>
    intro ot hsh hc
    cases hsh with
    | stuck => exact (hstuck hc).elim
    | guard t _ hS =>
      obtain ⟨l, u, ht, hL, hR'⟩ :=
        ih _ (Hshape _ _ hS) (by rw [fold_unfold]; exact (can_trans_guard t).1 hc)
      exact ⟨l, u, .guard ht, hL, hR'⟩
  | step =>
    intro ot hsh hc
    cases hsh with
    | stuck => exact (hstuck hc).elim
    | step t _ hS => exact ⟨.tau, t, .step, .tau, HS _ _ hS⟩
  | obs x' =>
    intro ot hsh hc
    cases hsh with
    | stuck => exact (hstuck hc).elim
    | vis e _ k _ he hY hk =>
      exact ⟨.obs e (cast hY.symm x'), k (cast hY.symm x'), .obs _,
        .obs _ _ _ _ he (cast_heq hY.symm x'), HS _ _ (hk _ _ (cast_heq hY.symm x'))⟩
  | val =>
    intro ot hsh hc
    cases hsh with
    | stuck => exact (hstuck hc).elim
    | ret x _ hx => exact ⟨.val x, .stuck, .val, .val _ _ hx, csim_stuck_l ER RV hR _⟩

/-- Every invariant pair with matching observations is a simulation, by finite induction on
`Trans_`. -/
theorem csim_structural : ∀ t t', S t t' → csim ER RV t t' := by
  refine gfp_prop (b := csimF ER RV) (P := fun R => ∀ t t', S t t' → R t t')
    (tower (fun T hT t t' h => Rel.inf_apply.2 fun R hR => hT R hR t t' h) ?_)
  intro R hR IH t t' h
  exact ⟨fun l u ht => csim_shape_trans_l ER RV S Hshape hR IH l _ u ht _ (Hshape _ _ h),
    fun hc l' u' ht' => csim_shape_trans_r ER RV S Hshape hR IH l' _ u' ht' _ (Hshape _ _ h)
      (by rw [fold_unfold]; exact hc)⟩

end StructuralSimulation

-- Not ported: `can_trans_equ`, `csim_chain_equ`, `guards_to_step_equ`, `framable_chain_equ`,
-- `csim_shape_transport`, `csim_shape_equ` (`equ` is `=`).

end Tisl
