/- SPDX-License-Identifier: MIT -/
module

public import Logic.Congruence

/-!
# Simulations of Kripke models

Shallow simulations between two Kripke structures relating models (`Fr`), events (`ER`) and return
values (`RV`) transport every TICL formula along `framer`, which relates every atom, including
prefix guards and predecessor worlds (← `Logic/Simulation.v`).
-/

@[expose] public section
namespace Tisl
open ITree (Effect)
open CTree.Coinduction

/-- Relations on events. The answers of related events are related by `HEq` where needed. -/
def event_rel (E : Effect.{u}) : Type u := E.I → E.I → Prop

variable {E : Effect.{u}} {X : Type u}

def event_eq : event_rel E := fun e e' => e = e'

def event_right_unique (ER : event_rel E) : Prop := ∀ e e1 e2, ER e e1 → ER e e2 → e1 = e2

/-- Uniqueness needed to transport return formulas (`b = true`); nothing for prefix formulas. -/
def sim_unique (b : Bool) (ER : event_rel E) (RV : X → X → Prop) : Prop :=
  if b then event_right_unique ER ∧ (∀ x y1 y2, RV x y1 → RV x y2 → y1 = y2) else True

theorem event_eq_right_unique : event_right_unique (event_eq (E := E)) :=
  fun _ _ _ h1 h2 => h1.symm.trans h2

theorem event_eq_refl (e : E.I) : event_eq e e := rfl

/-- Related worlds retain constructor shape; event answers are equal (as `HEq`). -/
inductive simW (ER : event_rel E) (RV : X → X → Prop) : World E → World E → Prop
  | pure : simW ER RV .pure .pure
  | obs (e e' : E.I) (v : E.O e) (v' : E.O e') :
      ER e e' → HEq v v' → simW ER RV (.obs e v) (.obs e' v')
  | done (x x' : X) : RV x x' → simW ER RV (.done x) (.done x')
  | finish (e e' : E.I) (v : E.O e) (v' : E.O e') (x x' : X) :
      ER e e' → HEq v v' → RV x x' → simW ER RV (.finish e v x) (.finish e' v' x')

section SimW
variable (ER : event_rel E) (RV : X → X → Prop)

theorem simW_not_done_iff {w w' : World E} (h : simW ER RV w w') : NotDone w ↔ NotDone w' := by
  cases h <;> simp

theorem simW_refl (hR : ∀ e, ER e e) (w : World E) (hw : NotDone w) : simW ER RV w w := by
  cases hw with
  | pure => exact .pure
  | obs e v => exact .obs e e v v (hR e) .rfl

theorem simW_not_done_right_unique (hU : event_right_unique ER) (w w1 w2 : World E)
    (hw : NotDone w) (h1 : simW ER RV w w1) (h2 : simW ER RV w w2) : w1 = w2 := by
  cases hw with
  | pure => cases h1; cases h2; rfl
  | obs e v =>
    cases h1 with | obs _ e1 _ v1 he1 hv1 =>
    cases h2 with | obs _ e2 _ v2 he2 hv2 =>
    obtain rfl := hU _ _ _ he1 he2
    cases hv1.symm.trans hv2
    rfl

theorem simW_event_eq_not_done (w w' : World E) (h : simW event_eq RV w w') (hw : NotDone w) :
    w' = w := by
  cases hw with
  | pure => cases h; rfl
  | obs e v =>
    cases h with | obs _ _ _ _ he hv =>
    cases he; cases hv; rfl

end SimW

/-! ## Framing formulas -/

/-- `framer` at an arbitrary index whose return atoms have type `X`. -/
def framerAux (ER : event_rel E) (RV : X → X → Prop) {i : Option (Type u)} (p : Ticl E i)
    (h : ∀ Y, i = some Y → Y = X) : Ticl E i :=
  mapAtomsAux (fun P w' => ∃ w, simW ER RV w w' ∧ P w)
    (fun P x' w' => ∃ x w, RV x x' ∧ simW ER RV w w' ∧ P x w) p h

/-- Every atom, including guards and predecessor worlds, is transported along `simW`. -/
def framer (X : Type u) (b : Bool) (ER : event_rel E) (RV : X → X → Prop) (p : TiclAt E X b) :
    TiclAt E X b :=
  map_atoms (fun P w' => ∃ w, simW ER RV w w' ∧ P w)
    (fun P x' w' => ∃ x w, RV x x' ∧ simW ER RV w w' ∧ P x w) b p

section Framer
variable (X : Type u) (ER : event_rel E) (RV : X → X → Prop)

theorem framer_now (P : World E → Prop) :
    framer X false ER RV (Ticl.now P) = Ticl.now fun w' => ∃ w, simW ER RV w w' ∧ P w := rfl
theorem framer_ret (P : X → World E → Prop) :
    framer X true ER RV (Ticl.ret P) =
      Ticl.ret fun x' w' => ∃ x w, RV x x' ∧ simW ER RV w w' ∧ P x w := rfl
theorem framer_u (b : Bool) (q : Ticlq) (p : TiclL E) (r : TiclAt E X b) :
    framer X b ER RV (.cu q p r) = .cu q (framer X false ER RV p) (framer X b ER RV r) := rfl
theorem framer_n (b : Bool) (q : Ticlq) (p : TiclL E) (r : TiclAt E X b) :
    framer X b ER RV (.cx q p r) = .cx q (framer X false ER RV p) (framer X b ER RV r) := rfl
theorem framer_g (q : Ticlq) (p : TiclL E) :
    framer X false ER RV (Ticl.cg q p) = Ticl.cg q (framer X false ER RV p) := rfl
theorem framer_and (b : Bool) (p r : TiclAt E X b) :
    framer X b ER RV (.and p r) = .and (framer X b ER RV p) (framer X b ER RV r) := rfl
theorem framer_or (b : Bool) (p r : TiclAt E X b) :
    framer X b ER RV (.or p r) = .or (framer X b ER RV p) (framer X b ER RV r) := rfl

end Framer

/-- `prefix_stable` at an arbitrary index (return atoms impose nothing). -/
def prefixStableAux (ER : event_rel E) (RV : X → X → Prop) : {i : Option (Type u)} → Ticl E i → Prop
  | _, .now P => ∀ w w', NotDone w → simW ER RV w w' → P w → P w'
  | _, .ret _ => True
  | _, .cu _ p r => prefixStableAux ER RV p ∧ prefixStableAux ER RV r
  | _, .cx _ p r => prefixStableAux ER RV p ∧ prefixStableAux ER RV r
  | _, .cg _ p => prefixStableAux ER RV p
  | _, .and p r => prefixStableAux ER RV p ∧ prefixStableAux ER RV r
  | _, .or p r => prefixStableAux ER RV p ∧ prefixStableAux ER RV r

/-- Every guard atom of a prefix formula is closed under `simW` from nonterminal worlds. -/
def prefix_stable (ER : event_rel E) (RV : X → X → Prop) (p : TiclL E) : Prop :=
  prefixStableAux ER RV p

section PrefixStable
variable (ER : event_rel E) (RV : X → X → Prop) (q : Ticlq) (p r : TiclL E)
@[simp] theorem prefix_stable_now (P : World E → Prop) :
    prefix_stable ER RV (.now P) ↔ ∀ w w', NotDone w → simW ER RV w w' → P w → P w' := .rfl
@[simp] theorem prefix_stable_cu :
    prefix_stable ER RV (.cu q p r) ↔ prefix_stable ER RV p ∧ prefix_stable ER RV r := .rfl
@[simp] theorem prefix_stable_cx :
    prefix_stable ER RV (.cx q p r) ↔ prefix_stable ER RV p ∧ prefix_stable ER RV r := .rfl
@[simp] theorem prefix_stable_cg : prefix_stable ER RV (.cg q p) ↔ prefix_stable ER RV p := .rfl
@[simp] theorem prefix_stable_and :
    prefix_stable ER RV (.and p r) ↔ prefix_stable ER RV p ∧ prefix_stable ER RV r := .rfl
@[simp] theorem prefix_stable_or :
    prefix_stable ER RV (.or p r) ↔ prefix_stable ER RV p ∧ prefix_stable ER RV r := .rfl
end PrefixStable

/-! ## Shallow simulations between two Kripke structures on the same models -/

section ShallowKripkeSim
variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {B : Effect.{u}}
  (KS KT : Kripke M E B) (ER : event_rel E) (RV : X → X → Prop)
  (Fr : M E B X → M E B X → Prop)
  (sim_l : ∀ t t' w w' t1 w1, Fr t t' → simW ER RV w w' → KS.ktrans t w t1 w1 →
    ∃ t1' w1', KT.ktrans t' w' t1' w1' ∧ Fr t1 t1' ∧ simW ER RV w1 w1')
  (sim_r : ∀ t t' w w' t1' w1', Fr t t' → simW ER RV w w' → @can_step M E B KS X t w →
    KT.ktrans t' w' t1' w1' → ∃ t1 w1, KS.ktrans t w t1 w1 ∧ Fr t1 t1' ∧ simW ER RV w1 w1')
include sim_l

theorem sim_can_step (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : @can_step M E B KS X t w) : @can_step M E B KT X t' w' :=
  let ⟨_, _, hT⟩ := h
  let ⟨t1', w1', hT', _⟩ := sim_l _ _ _ _ _ _ hF hW hT
  ⟨t1', w1', hT'⟩

section Binary
variable (P P' Q Q' : M E B X → World E → Prop)
  (HP : ∀ t t' w w', Fr t t' → simW ER RV w w' → P t w → P' t' w')
  (HQ : ∀ t t' w w', Fr t t' → simW ER RV w w' → Q t w → Q' t' w')
include HP HQ

include sim_r in
theorem sim_anc (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : @anc M E B KS X P Q t w) : @anc M E B KT X P' Q' t' w' := by
  obtain ⟨hp, hs, hN⟩ := h
  refine ⟨HP _ _ _ _ hF hW hp, sim_can_step KS KT ER RV Fr sim_l _ _ _ _ hF hW hs, ?_⟩
  intro t1' w1' hT'
  obtain ⟨t1, w1, hT, hF1, hW1⟩ := sim_r _ _ _ _ _ _ hF hW hs hT'
  exact HQ _ _ _ _ hF1 hW1 (hN _ _ hT)

theorem sim_enc (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : @enc M E B KS X P Q t w) : @enc M E B KT X P' Q' t' w' := by
  obtain ⟨hp, t1, w1, hT, hq⟩ := h
  obtain ⟨t1', w1', hT', hF1, hW1⟩ := sim_l _ _ _ _ _ _ hF hW hT
  exact ⟨HP _ _ _ _ hF hW hp, t1', w1', hT', HQ _ _ _ _ hF1 hW1 hq⟩

include sim_r in
theorem sim_auc (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : @Auc M E B KS X P Q t w) : @Auc M E B KT X P' Q' t' w' := by
  induction h generalizing t' w' with
  | matchA hq => exact .matchA (HQ _ _ _ _ hF hW hq)
  | stepA hp hs _ ih =>
    refine .stepA (HP _ _ _ _ hF hW hp) (sim_can_step KS KT ER RV Fr sim_l _ _ _ _ hF hW hs) ?_
    intro t1' w1' hT'
    obtain ⟨t1, w1, hT, hF1, hW1⟩ := sim_r _ _ _ _ _ _ hF hW hs hT'
    exact ih t1 w1 hT t1' w1' hF1 hW1

theorem sim_euc (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : @Euc M E B KS X P Q t w) : @Euc M E B KT X P' Q' t' w' := by
  induction h generalizing t' w' with
  | matchE hq => exact .matchE (HQ _ _ _ _ hF hW hq)
  | stepE t1 w1 hp hT _ ih =>
    obtain ⟨t1', w1', hT', hF1, hW1⟩ := sim_l _ _ _ _ _ _ hF hW hT
    exact .stepE t1' w1' (HP _ _ _ _ hF hW hp) hT' (ih _ _ hF1 hW1)

end Binary

section Always
variable (P P' : M E B X → World E → Prop)
  (HP : ∀ t t' w w', Fr t t' → simW ER RV w w' → P t w → P' t' w')
include HP

include sim_r in
theorem sim_agc (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : gfp (@agcF M E B KS X P) t w) : gfp (@agcF M E B KT X P') t' w' :=
  le_gfp (b := @agcF M E B KT X P')
    (x := fun t' w' => ∃ t w, Fr t t' ∧ simW ER RV w w' ∧ gfp (@agcF M E B KS X P) t w)
    (fun t' w' ⟨t, w, hF, hW, h⟩ =>
      sim_anc KS KT ER RV Fr sim_l sim_r P P' _ _ HP (fun t _ w _ hF hW h => ⟨t, w, hF, hW, h⟩)
        t t' w w' hF hW (gfp_pfp (b := @agcF M E B KS X P) t w h))
    t' w' ⟨t, w, hF, hW, h⟩

include sim_r in
theorem sim_agc_chain (R : Rel (M E B X) (World E)) (hR : Chain (@agcF M E B KT X P') R)
    (t t' w w') (hF : Fr t t') (hW : simW ER RV w w') (h : gfp (@agcF M E B KS X P) t w) :
    R t' w' :=
  gfp_le_chain hR t' w' (sim_agc KS KT ER RV Fr sim_l sim_r P P' HP t t' w w' hF hW h)

theorem sim_egc (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : gfp (@egcF M E B KS X P) t w) : gfp (@egcF M E B KT X P') t' w' :=
  le_gfp (b := @egcF M E B KT X P')
    (x := fun t' w' => ∃ t w, Fr t t' ∧ simW ER RV w w' ∧ gfp (@egcF M E B KS X P) t w)
    (fun t' w' ⟨t, w, hF, hW, h⟩ =>
      sim_enc KS KT ER RV Fr sim_l P P' _ _ HP (fun t _ w _ hF hW h => ⟨t, w, hF, hW, h⟩)
        t t' w w' hF hW (gfp_pfp (b := @egcF M E B KS X P) t w h))
    t' w' ⟨t, w, hF, hW, h⟩

theorem sim_egc_chain (R : Rel (M E B X) (World E)) (hR : Chain (@egcF M E B KT X P') R)
    (t t' w w') (hF : Fr t t') (hW : simW ER RV w w') (h : gfp (@egcF M E B KS X P) t w) :
    R t' w' :=
  gfp_le_chain hR t' w' (sim_egc KS KT ER RV Fr sim_l P P' HP t t' w w' hF hW h)

end Always
end ShallowKripkeSim

/-! ## Transport of formulas along a simulation -/

section DoneTransport
variable (ER : event_rel E) (RV : X → X → Prop)

theorem sim_done_with (P : X → World E → Prop) (w w' : World E) (hW : simW ER RV w w')
    (hD : DoneWith P w) :
    DoneWith (fun x' z' => ∃ x z, RV x x' ∧ simW ER RV z z' ∧ P x z) w' := by
  cases hD with
  | done x h => cases hW with | done _ x' hR => exact .done x' ⟨x, .pure, hR, .pure, h⟩
  | finish e v x h =>
    cases hW with
    | finish _ e' _ v' _ x' he hv hR =>
      exact .finish e' v' x' ⟨x, .obs e v, hR, .obs e e' v v' he hv, h⟩

theorem sim_done_of (x : X) (w z z' : World E) (hW : simW ER RV z z') (hD : DoneOf x w z) :
    ∃ x' q', RV x x' ∧ simW ER RV w q' ∧ DoneOf x' q' z' := by
  cases hD with
  | pure => cases hW with | done _ x' hR => exact ⟨x', .pure, hR, .pure, .pure⟩
  | obs e v =>
    cases hW with
    | finish _ e' _ v' _ x' he hv hR => exact ⟨x', .obs e' v', hR, .obs e e' v v' he hv, .obs e' v'⟩

end DoneTransport

section KripkeSim
variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {B : Effect.{u}} [K : Kripke M E B]
  (ER : event_rel E) (RV : X → X → Prop) (Fr : M E B X → M E B X → Prop)
  (sim_l : ∀ t t' w w' t1 w1, Fr t t' → simW ER RV w w' → ktrans t w t1 w1 →
    ∃ t1' w1', ktrans t' w' t1' w1' ∧ Fr t1 t1' ∧ simW ER RV w1 w1')
  (sim_r : ∀ t t' w w' t1' w1', Fr t t' → simW ER RV w w' → can_step t w →
    ktrans t' w' t1' w1' → ∃ t1 w1, ktrans t w t1 w1 ∧ Fr t1 t1' ∧ simW ER RV w1 w1')
include sim_l sim_r

/-- `ticl_sim` at an arbitrary index; return atoms need the uniqueness of `sim_unique true`. -/
theorem ticl_sim_aux {i : Option (Type u)} (p : Ticl E i) (h : ∀ Y, i = some Y → Y = X)
    (hu : i ≠ none → sim_unique true ER RV) :
    ∀ t t' w w', Fr t t' → simW ER RV w w' → entails p t w →
      entails (framerAux ER RV p h) t' w' := by
  induction p with
  | now P =>
    intro t t' w w' _ hW ⟨hp, hd⟩
    exact ⟨⟨w, hW, hp⟩, (simW_not_done_iff ER RV hW).1 hd⟩
  | @ret Y P =>
    obtain rfl := h Y rfl
    obtain ⟨hEU, hRU⟩ := hu nofun
    intro t t' w w' hF hW ⟨x, hp, hnd, ⟨u, z, hT⟩, hN⟩
    obtain ⟨u', z', hT', -, hW1⟩ := sim_l _ _ _ _ _ _ hF hW hT
    obtain ⟨x', q', hR, hQ, -⟩ := sim_done_of ER RV x w _ _ hW1 (hN _ _ hT)
    obtain rfl := simW_not_done_right_unique ER RV hEU w q' w' hnd hQ hW
    refine ⟨x', ⟨x, w, hR, hW, hp⟩, (simW_not_done_iff ER RV hW).1 hnd, ⟨u', z', hT'⟩, ?_⟩
    intro v' r' hV'
    obtain ⟨v, r, hV, -, hW2⟩ := sim_r _ _ _ _ _ _ hF hW ⟨u, z, hT⟩ hV'
    obtain ⟨y, q, hRy, hQy, hDy⟩ := sim_done_of ER RV x w _ _ hW2 (hN _ _ hV)
    obtain rfl := simW_not_done_right_unique ER RV hEU w q q' hnd hQy hW
    obtain rfl := hRU x y x' hRy hR
    exact hDy
  | cu q p r ihp ihr =>
    intro t t' w w' hF hW H
    have hp := ihp nofun nofun
    have hr := ihr h hu
    cases q
    · exact sim_auc K K ER RV Fr sim_l sim_r _ _ _ _ hp hr t t' w w' hF hW H
    · exact sim_euc K K ER RV Fr sim_l _ _ _ _ hp hr t t' w w' hF hW H
  | cx q p r ihp ihr =>
    intro t t' w w' hF hW H
    have hp := ihp nofun nofun
    have hr := ihr h hu
    cases q
    · exact sim_anc K K ER RV Fr sim_l sim_r _ _ _ _ hp hr t t' w w' hF hW H
    · exact sim_enc K K ER RV Fr sim_l _ _ _ _ hp hr t t' w w' hF hW H
  | cg q p ihp =>
    intro t t' w w' hF hW H
    have hp := ihp h hu
    cases q
    · exact sim_agc K K ER RV Fr sim_l sim_r _ _ hp t t' w w' hF hW H
    · exact sim_egc K K ER RV Fr sim_l _ _ hp t t' w w' hF hW H
  | and p r ihp ihr =>
    intro t t' w w' hF hW H
    exact ⟨ihp h hu t t' w w' hF hW H.1, ihr h hu t t' w w' hF hW H.2⟩
  | or p r ihp ihr =>
    intro t t' w w' hF hW H
    exact H.imp (ihp h hu t t' w w' hF hW) (ihr h hu t t' w w' hF hW)

theorem ticll_sim (p : TiclL E) (t t' w w') (hF : Fr t t') (hW : simW ER RV w w')
    (h : entails p t w) : entails (framer X false ER RV p) t' w' :=
  ticl_sim_aux ER RV Fr sim_l sim_r p (ticlAt_ret_type false) nofun t t' w w' hF hW h

theorem ticl_sim (b : Bool) (p : TiclAt E X b) (hu : sim_unique b ER RV) (t t' w w')
    (hF : Fr t t') (hW : simW ER RV w w') (h : entails p t w) :
    entails (framer X b ER RV p) t' w' := by
  refine ticl_sim_aux ER RV Fr sim_l sim_r p (ticlAt_ret_type b) ?_ t t' w w' hF hW h
  intro hne
  cases b
  · exact absurd rfl hne
  · exact hu

end KripkeSim

/-! ## Atomic transport -/

section AtomicTransport
variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {B : Effect.{u}} [Kripke M E B]

theorem prefix_stable_framer (X : Type u) (ER : event_rel E) (RV : X → X → Prop) (p : TiclL E)
    (hS : prefix_stable ER RV p) : impl_ticl M B X (framer X false ER RV p) p := by
  suffices H : ∀ {i} (p : Ticl E i) (h : ∀ Y, i = some Y → Y = X), i = none →
      prefixStableAux ER RV p → impl_ticl M B X (framerAux ER RV p h) p from
    H p (ticlAt_ret_type false) rfl hS
  intro i p
  induction p with
  | now P =>
    intro _ _ hS t w ⟨⟨z, hW, hP⟩, hnd⟩
    exact ⟨hS z w ((simW_not_done_iff ER RV hW).2 hnd) hW hP, hnd⟩
  | ret P => intro _ hi; cases hi
  | cu q p r ihp ihr =>
    intro h hi hS; exact impl_ticl_until q (ihp nofun rfl hS.1) (ihr h hi hS.2)
  | cx q p r ihp ihr =>
    intro h hi hS; exact impl_ticl_next q (ihp nofun rfl hS.1) (ihr h hi hS.2)
  | cg q p ihp => intro h hi hS; exact impl_ticl_global q (ihp h hi hS)
  | and p r ihp ihr => intro h hi hS; exact impl_ticl_and (ihp h hi hS.1) (ihr h hi hS.2)
  | or p r ihp ihr => intro h hi hS; exact impl_ticl_or (ihp h hi hS.1) (ihr h hi hS.2)

/-- With equality of events, `framer` only relates returned values. -/
theorem framer_event_eq (X : Type u) (b : Bool) (RV : X → X → Prop) (p : TiclAt E X b)
    (t : M E B X) (w : World E) :
    entails (framer X b event_eq RV p) t w ↔
      (match b, p with
       | false, f => entails f t w
       | true, f => entails (map_ret (fun P x' z => ∃ x, RV x x' ∧ P x z) f) t w) := by
  have hP : ∀ {i} (p : Ticl E i) (h : ∀ Y, i = some Y → Y = X), i = none →
      equiv_ticl M B X (framerAux event_eq RV p h) p := by
    intro i p
    induction p with
    | now P =>
      intro _ _
      refine ⟨fun t w ⟨⟨z, hW, hP⟩, hnd⟩ => ?_, fun t w ⟨hP, hnd⟩ => ?_⟩
      · obtain rfl :=
          simW_event_eq_not_done RV z w hW ((simW_not_done_iff event_eq RV hW).2 hnd)
        exact ⟨hP, hnd⟩
      · exact ⟨⟨w, simW_refl event_eq RV event_eq_refl w hnd, hP⟩, hnd⟩
    | ret P => intro _ hi; cases hi
    | cu q p r ihp ihr => intro h hi; exact equiv_ticl_until q (ihp nofun rfl) (ihr h hi)
    | cx q p r ihp ihr => intro h hi; exact equiv_ticl_next q (ihp nofun rfl) (ihr h hi)
    | cg q p ihp => intro h hi; exact equiv_ticl_global q (ihp h hi)
    | and p r ihp ihr => intro h hi; exact equiv_ticl_and (ihp h hi) (ihr h hi)
    | or p r ihp ihr => intro h hi; exact equiv_ticl_or (ihp h hi) (ihr h hi)
  have hR : ∀ {i} (p : Ticl E i) (h : ∀ Y, i = some Y → Y = X) (hi : i = some X) t w,
      entails (framerAux event_eq RV p h) t w ↔
        entails (mapRetAux (fun P x' z => ∃ x, RV x x' ∧ P x z) p hi) (t : M E B X) w := by
    intro i p
    induction p with
    | now P => intro _ hi; cases hi
    | @ret Y P =>
      intro h hi
      cases hi
      intro t w
      refine ⟨fun ⟨x', ⟨x, z, hR, hW, hP⟩, ha⟩ => ?_, fun ⟨x', ⟨x, hR, hP⟩, ha⟩ => ?_⟩
      · have hnd := anc_not_done ha
        obtain rfl :=
          simW_event_eq_not_done RV z w hW ((simW_not_done_iff event_eq RV hW).2 hnd)
        exact ⟨x', ⟨x, hR, hP⟩, ha⟩
      · exact ⟨x', ⟨x, w, hR, simW_refl event_eq RV event_eq_refl w (anc_not_done ha), hP⟩, ha⟩
    | cu q p r ihp ihr =>
      intro h hi t w
      subst hi
      exact equiv_ticl_entails (equiv_ticl_until q (hP p nofun rfl)
        ⟨fun t w => (ihr h rfl t w).1, fun t w => (ihr h rfl t w).2⟩)
    | cx q p r ihp ihr =>
      intro h hi t w
      subst hi
      exact equiv_ticl_entails (equiv_ticl_next q (hP p nofun rfl)
        ⟨fun t w => (ihr h rfl t w).1, fun t w => (ihr h rfl t w).2⟩)
    | cg q p ihp => intro _ hi; cases hi
    | and p r ihp ihr =>
      intro h hi t w
      subst hi
      exact and_congr (ihp h rfl t w) (ihr h rfl t w)
    | or p r ihp ihr =>
      intro h hi t w
      subst hi
      exact or_congr (ihp h rfl t w) (ihr h rfl t w)
  cases b
  · exact equiv_ticl_entails (hP p (ticlAt_ret_type false) rfl)
  · exact hR p (ticlAt_ret_type true) rfl t w

end AtomicTransport

end Tisl
