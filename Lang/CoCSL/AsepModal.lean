/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.OwnedInterp
public import Logic.Setoid
public import Lang.CoCSL.Sequential

/-!
# Modalities over a bare transition relation on owned configurations

A transition relation on states is a Kripke model with no observations; the `h*` modalities are
TICL's `anc`/`enc`/`Auc`/`Euc`/`agc`/`egc` at the `pure` world over that model. Unfoldings,
monotonicity, properness under `owned_equ` and selection stability of view predicates
(← `Lang/CoCSL/Asep.v`, lines 1-389).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Pcm Coinduction
open ITree (Effect)

/-! ## A Kripke model of a bare transition relation -/

abbrev StateModel (S : Type) (_E _B : Effect.{0}) (_X : Type) : Type := S

/-- No observations: every world is `pure`. -/
def NoObs : Effect.{0} := ⟨PEmpty, fun e => e.elim⟩

@[instance_reducible]
def rel_kripke {S : Type} (R : S → S → Prop) : Kripke (StateModel S) NoObs Bn where
  ktrans s w s' w' := w = .pure ∧ w' = .pure ∧ R s s'
  ktrans_not_done h := h.1 ▸ .pure

theorem rel_ktrans {S : Type} (R : S → S → Prop) {X : Type} {s s' : S} {w w' : World NoObs} :
    @ktrans _ _ _ (rel_kripke R) X s w s' w' ↔ w = .pure ∧ w' = .pure ∧ R s s' := Iff.rfl

/-- Leibniz equality is a model equality for any relation. -/
instance rel_kripke_setoid {S : Type} (R : S → S → Prop) (X : Type) :
    @KripkeSetoid (StateModel S) NoObs Bn (rel_kripke R) X Eq :=
  @KripkeSetoid.mk _ _ _ (rel_kripke R) _ _ ⟨Eq.refl, Eq.symm, Eq.trans⟩
    fun h tr => ⟨_, h ▸ tr, rfl⟩

abbrev hprop := OwnedCfg → Prop

def hlift (P : hprop) : StateModel OwnedCfg NoObs Bn Unit → World NoObs → Prop :=
  fun c _ => P c

def hAN (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) : hprop :=
  fun c => @anc _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure
def hEN (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) : hprop :=
  fun c => @enc _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure
def hAU (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) : hprop :=
  fun c => @Auc _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure
def hEU (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) : hprop :=
  fun c => @Euc _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure
def hAG (R : OwnedCfg → OwnedCfg → Prop) (P : hprop) : hprop :=
  fun c => gfp (@agcF _ _ _ (rel_kripke R) Unit (hlift P)) c .pure
def hEG (R : OwnedCfg → OwnedCfg → Prop) (P : hprop) : hprop :=
  fun c => gfp (@egcF _ _ _ (rel_kripke R) Unit (hlift P)) c .pure

def hTrue : hprop := fun _ => True
def hAX (R : OwnedCfg → OwnedCfg → Prop) (Q : hprop) : hprop := hAN R hTrue Q
def hEX (R : OwnedCfg → OwnedCfg → Prop) (Q : hprop) : hprop := hEN R hTrue Q
def hAF (R : OwnedCfg → OwnedCfg → Prop) (Q : hprop) : hprop := hAU R hTrue Q
def hEF (R : OwnedCfg → OwnedCfg → Prop) (Q : hprop) : hprop := hEU R hTrue Q
def hand (P Q : hprop) : hprop := fun c => P c ∧ Q c
def hor (P Q : hprop) : hprop := fun c => P c ∨ Q c

/-! ## Termination and results -/

def terminal (c : OwnedCfg) : Prop := c.pool.size = 0

/-- A live-state atom. -/
def hNow (P : hprop) : hprop := fun c => ¬ terminal c ∧ P c

/-- Already finished, versus uniformly finishing on the next step (`hRet`). -/
def hDone (P : hprop) : hprop := fun c => terminal c ∧ P c

def hRet (R : OwnedCfg → OwnedCfg → Prop) (P : hprop) : hprop :=
  fun c => ∃ out, R c out ∧ ∀ d, R c d → terminal d ∧ same_view d out ∧ P d

/-! ## Ordinary heap separation lifted to owned states -/

/-- A predicate read on one lineage's projection. -/
def at_side (i : Side) (P : hprop) : hprop := fun c => P (project i c)

def hproper (P : hprop) : Prop := ∀ c d, owned_equ c d → (P c ↔ P d)

def view_pred (P : hprop) : Prop := ∀ c d, same_view c d → P c → P d

def SelectionStable (Q : hprop) : Prop :=
  ∀ d a d', owned_step d a d' → a.action_kind = .select → (Q d ↔ Q d')

def hRet_at (i : Side) (R : OwnedCfg → OwnedCfg → Prop) (P : hprop) : hprop :=
  fun c => ∃ out, R c out ∧ ∀ d, R c d → terminal (project i d) ∧
    same_view (project i d) (project i out) ∧ P (project i d)

/-! ## Model equality for the owned clocks -/

instance owned_next_setoid :
    @KripkeSetoid (StateModel OwnedCfg) NoObs Bn (rel_kripke owned_next) Unit owned_equ :=
  @KripkeSetoid.mk _ _ _ (rel_kripke owned_next) _ _ owned_equ_Equivalence
    fun {_ _ s' _ _} E ⟨h1, h2, TR⟩ =>
      let ⟨d', TR', E'⟩ := owned_next_equ _ _ s' E TR; ⟨d', ⟨h1, h2, TR'⟩, E'⟩

instance weak_next_setoid (i : Side) :
    @KripkeSetoid (StateModel OwnedCfg) NoObs Bn (rel_kripke (weak_next i)) Unit owned_equ :=
  @KripkeSetoid.mk _ _ _ (rel_kripke (weak_next i)) _ _ owned_equ_Equivalence
    fun {_ _ s' _ _} E ⟨h1, h2, TR⟩ =>
      let ⟨d', TR', E'⟩ := weak_next_equ i _ _ s' E TR; ⟨d', ⟨h1, h2, TR'⟩, E'⟩

/-! ## Unfoldings -/

theorem can_step_rel (R : OwnedCfg → OwnedCfg → Prop) (c : OwnedCfg) :
    @can_step _ _ _ (rel_kripke R) Unit c .pure ↔ hcan_step R c :=
  ⟨fun ⟨c', _, _, _, TR⟩ => ⟨c', TR⟩, fun ⟨c', TR⟩ => ⟨c', .pure, rfl, rfl, TR⟩⟩

private theorem anc_rel_iff (R : OwnedCfg → OwnedCfg → Prop)
    (p q : StateModel OwnedCfg NoObs Bn Unit → World NoObs → Prop) (c : OwnedCfg) :
    @anc _ _ _ (rel_kripke R) Unit p q c .pure ↔
      p c .pure ∧ hcan_step R c ∧ ∀ c', R c c' → q c' .pure :=
  ⟨fun ⟨Hp, Hs, H⟩ => ⟨Hp, (can_step_rel R c).1 Hs, fun c' TR => H c' .pure ⟨rfl, rfl, TR⟩⟩,
   fun ⟨Hp, Hs, H⟩ => ⟨Hp, (can_step_rel R c).2 Hs, fun c' _ ⟨_, hw, TR⟩ => hw ▸ H c' TR⟩⟩

private theorem enc_rel_iff (R : OwnedCfg → OwnedCfg → Prop)
    (p q : StateModel OwnedCfg NoObs Bn Unit → World NoObs → Prop) (c : OwnedCfg) :
    @enc _ _ _ (rel_kripke R) Unit p q c .pure ↔ p c .pure ∧ ∃ c', R c c' ∧ q c' .pure :=
  ⟨fun ⟨Hp, c', _, ⟨_, hw, TR⟩, HQ⟩ => ⟨Hp, c', TR, hw ▸ HQ⟩,
   fun ⟨Hp, c', TR, HQ⟩ => ⟨Hp, c', .pure, ⟨rfl, rfl, TR⟩, HQ⟩⟩

theorem hAN_iff (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) (c : OwnedCfg) :
    hAN R P Q c ↔ P c ∧ hcan_step R c ∧ ∀ c', R c c' → Q c' :=
  anc_rel_iff R _ _ c

theorem hEN_iff (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) (c : OwnedCfg) :
    hEN R P Q c ↔ P c ∧ ∃ c', R c c' ∧ Q c' :=
  enc_rel_iff R _ _ c

theorem hAU_now (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) (c : OwnedCfg) :
    Q c → hAU R P Q c := @Auc.matchA _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure

theorem hAU_step (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) (c : OwnedCfg) :
    P c → hcan_step R c → (∀ c', R c c' → hAU R P Q c') → hAU R P Q c := fun Hp Hs H =>
  @Auc.stepA _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure Hp ((can_step_rel R c).2 Hs)
    fun c' _ ⟨_, hw, TR⟩ => hw ▸ H c' TR

theorem hAU_ind (R : OwnedCfg → OwnedCfg → Prop) (P Q Z : hprop) (hb : ∀ c, Q c → Z c)
    (hs : ∀ c, P c → hcan_step R c → (∀ c', R c c' → hAU R P Q c') →
      (∀ c', R c c' → Z c') → Z c) :
    ∀ c, hAU R P Q c → Z c := fun c H =>
  @auc_ind _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) (fun c w => w = .pure → Z c)
    (fun d _ hq _ => hb d hq)
    (fun d w ⟨hp, hc, hk⟩ ⟨_, _, ih⟩ hw => by
      subst hw
      exact hs d hp ((can_step_rel R d).1 hc) (fun c' TR => hk c' .pure ⟨rfl, rfl, TR⟩)
        fun c' TR => ih c' .pure ⟨rfl, rfl, TR⟩ rfl)
    c .pure H rfl

theorem hEU_now (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) (c : OwnedCfg) :
    Q c → hEU R P Q c := @Euc.matchE _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure

theorem hEU_step (R : OwnedCfg → OwnedCfg → Prop) (P Q : hprop) (c c' : OwnedCfg) :
    P c → R c c' → hEU R P Q c' → hEU R P Q c := fun Hp TR H =>
  @Euc.stepE _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) c .pure c' .pure Hp ⟨rfl, rfl, TR⟩ H

theorem hEU_ind (R : OwnedCfg → OwnedCfg → Prop) (P Q Z : hprop) (hb : ∀ c, Q c → Z c)
    (hs : ∀ c c', P c → R c c' → hEU R P Q c' → Z c' → Z c) :
    ∀ c, hEU R P Q c → Z c := fun c H =>
  @euc_ind _ _ _ (rel_kripke R) Unit (hlift P) (hlift Q) (fun c w => w = .pure → Z c)
    (fun d _ hq _ => hb d hq)
    (fun d w ⟨hp, c', _, tr, h, ih⟩ hw => by
      subst hw
      obtain ⟨-, rfl, TR⟩ := (rel_ktrans R).1 tr
      exact hs d c' hp TR h (ih rfl))
    c .pure H rfl

theorem hAG_unfold (R : OwnedCfg → OwnedCfg → Prop) (P : hprop) (c : OwnedCfg) :
    hAG R P c ↔ P c ∧ hcan_step R c ∧ ∀ c', R c c' → hAG R P c' :=
  (@agc_unfold _ _ _ (rel_kripke R) Unit (hlift P) c .pure).trans (anc_rel_iff R _ _ c)

theorem hAG_coind (R : OwnedCfg → OwnedCfg → Prop) (P I : hprop)
    (H : ∀ c, I c → P c ∧ hcan_step R c ∧ ∀ c', R c c' → I c') :
    ∀ c, I c → hAG R P c := fun c Hc =>
  le_gfp (b := @agcF _ _ _ (rel_kripke R) Unit (hlift P)) (x := fun d w => w = .pure ∧ I d)
    (fun d w ⟨hw, Hd⟩ => by
      subst hw
      obtain ⟨Hp, Hs, HN⟩ := H d Hd
      exact (anc_rel_iff R (hlift P) (fun d w => w = .pure ∧ I d) d).2
        ⟨Hp, Hs, fun c' TR => ⟨rfl, HN c' TR⟩⟩)
    c .pure ⟨rfl, Hc⟩

theorem hEG_unfold (R : OwnedCfg → OwnedCfg → Prop) (P : hprop) (c : OwnedCfg) :
    hEG R P c ↔ P c ∧ ∃ c', R c c' ∧ hEG R P c' :=
  (@egc_unfold _ _ _ (rel_kripke R) Unit (hlift P) c .pure).trans (enc_rel_iff R _ _ c)

theorem hEG_coind (R : OwnedCfg → OwnedCfg → Prop) (P I : hprop)
    (H : ∀ c, I c → P c ∧ ∃ c', R c c' ∧ I c') :
    ∀ c, I c → hEG R P c := fun c Hc =>
  le_gfp (b := @egcF _ _ _ (rel_kripke R) Unit (hlift P)) (x := fun d w => w = .pure ∧ I d)
    (fun d w ⟨hw, Hd⟩ => by
      subst hw
      obtain ⟨Hp, c', TR, Hc'⟩ := H d Hd
      exact (enc_rel_iff R (hlift P) (fun d w => w = .pure ∧ I d) d).2 ⟨Hp, c', TR, rfl, Hc'⟩)
    c .pure ⟨rfl, Hc⟩

theorem hAN_mono (R : OwnedCfg → OwnedCfg → Prop) (P P' Q Q' : hprop) (c : OwnedCfg)
    (HP : ∀ d, P d → P' d) (HQ : ∀ d, Q d → Q' d) : hAN R P Q c → hAN R P' Q' c := fun H =>
  let ⟨Hp, Hs, H⟩ := (hAN_iff R P Q c).1 H
  (hAN_iff R P' Q' c).2 ⟨HP _ Hp, Hs, fun c' TR => HQ _ (H c' TR)⟩

theorem hEN_mono (R : OwnedCfg → OwnedCfg → Prop) (P P' Q Q' : hprop) (c : OwnedCfg)
    (HP : ∀ d, P d → P' d) (HQ : ∀ d, Q d → Q' d) : hEN R P Q c → hEN R P' Q' c := fun H =>
  let ⟨Hp, c', TR, H⟩ := (hEN_iff R P Q c).1 H
  (hEN_iff R P' Q' c).2 ⟨HP _ Hp, c', TR, HQ _ H⟩

theorem hAU_mono (R : OwnedCfg → OwnedCfg → Prop) (P P' Q Q' : hprop) (c : OwnedCfg)
    (HP : ∀ d, P d → P' d) (HQ : ∀ d, Q d → Q' d) : hAU R P Q c → hAU R P' Q' c :=
  hAU_ind R P Q (hAU R P' Q') (fun d h => hAU_now R _ _ d (HQ d h))
    (fun d hp hs _ ih => hAU_step R _ _ d (HP d hp) hs ih) c

theorem hEU_mono (R : OwnedCfg → OwnedCfg → Prop) (P P' Q Q' : hprop) (c : OwnedCfg)
    (HP : ∀ d, P d → P' d) (HQ : ∀ d, Q d → Q' d) : hEU R P Q c → hEU R P' Q' c :=
  hEU_ind R P Q (hEU R P' Q') (fun d h => hEU_now R _ _ d (HQ d h))
    (fun d d' hp TR _ ih => hEU_step R _ _ d d' (HP d hp) TR ih) c

theorem hAG_mono (R : OwnedCfg → OwnedCfg → Prop) (P P' : hprop) (c : OwnedCfg)
    (HP : ∀ d, P d → P' d) : hAG R P c → hAG R P' c :=
  hAG_coind R P' (hAG R P) (fun d H =>
    let ⟨Hp, Hs, HN⟩ := (hAG_unfold R P d).1 H; ⟨HP d Hp, Hs, HN⟩) c

theorem hEG_mono (R : OwnedCfg → OwnedCfg → Prop) (P P' : hprop) (c : OwnedCfg)
    (HP : ∀ d, P d → P' d) : hEG R P c → hEG R P' c :=
  hEG_coind R P' (hEG R P) (fun d H =>
    let ⟨Hp, HN⟩ := (hEG_unfold R P d).1 H; ⟨HP d Hp, HN⟩) c

/-! ## Properness under `owned_equ` -/

theorem hlift_proper (P : hprop) (HP : hproper P) :
    ∀ t u w, owned_equ t u → (hlift P t w ↔ hlift P u w) := fun t u _ E => HP t u E

section Proper
variable {R : OwnedCfg → OwnedCfg → Prop}
  [KS : @KripkeSetoid (StateModel OwnedCfg) NoObs Bn (rel_kripke R) Unit owned_equ]

theorem hAN_proper_gen (P Q : hprop) (HP : hproper P) (HQ : hproper Q) :
    hproper (hAN R P Q) := fun _ _ E =>
  @proper_ax_equ _ _ _ (rel_kripke R) _ _ KS _ _ (hlift_proper P HP) (hlift_proper Q HQ) _ _ _ E

theorem hEN_proper_gen (P Q : hprop) (HP : hproper P) (HQ : hproper Q) :
    hproper (hEN R P Q) := fun _ _ E =>
  @proper_ex_equ _ _ _ (rel_kripke R) _ _ KS _ _ (hlift_proper P HP) (hlift_proper Q HQ) _ _ _ E

theorem hAU_proper_gen (P Q : hprop) (HP : hproper P) (HQ : hproper Q) :
    hproper (hAU R P Q) := fun _ _ E =>
  @proper_au_equ _ _ _ (rel_kripke R) _ _ KS _ _ (hlift_proper P HP) (hlift_proper Q HQ) _ _ _ E

theorem hEU_proper_gen (P Q : hprop) (HP : hproper P) (HQ : hproper Q) :
    hproper (hEU R P Q) := fun _ _ E =>
  @proper_eu_equ _ _ _ (rel_kripke R) _ _ KS _ _ (hlift_proper P HP) (hlift_proper Q HQ) _ _ _ E

theorem hAG_proper_gen (P : hprop) (HP : hproper P) : hproper (hAG R P) := fun _ _ E =>
  @proper_ag_equ _ _ _ (rel_kripke R) _ _ KS _ (hlift_proper P HP) _ _ _ E

theorem hEG_proper_gen (P : hprop) (HP : hproper P) : hproper (hEG R P) := fun _ _ E =>
  @proper_er_equ _ _ _ (rel_kripke R) _ _ KS _ (hlift_proper P HP) _ _ _ E

end Proper

theorem hAN_proper (P Q : hprop) : hproper P → hproper Q → hproper (hAN owned_next P Q) :=
  hAN_proper_gen P Q
theorem hEN_proper (P Q : hprop) : hproper P → hproper Q → hproper (hEN owned_next P Q) :=
  hEN_proper_gen P Q
theorem hAU_proper (P Q : hprop) : hproper P → hproper Q → hproper (hAU owned_next P Q) :=
  hAU_proper_gen P Q
theorem hEU_proper (P Q : hprop) : hproper P → hproper Q → hproper (hEU owned_next P Q) :=
  hEU_proper_gen P Q
theorem hAG_proper (P : hprop) : hproper P → hproper (hAG owned_next P) := hAG_proper_gen P
theorem hEG_proper (P : hprop) : hproper P → hproper (hEG owned_next P) := hEG_proper_gen P
theorem hAN_weak_proper (i : Side) (P Q : hprop) :
    hproper P → hproper Q → hproper (hAN (weak_next i) P Q) := hAN_proper_gen P Q
theorem hAU_weak_proper (i : Side) (P Q : hprop) :
    hproper P → hproper Q → hproper (hAU (weak_next i) P Q) := hAU_proper_gen P Q
theorem hAG_weak_proper (i : Side) (P : hprop) :
    hproper P → hproper (hAG (weak_next i) P) := hAG_proper_gen P

theorem owned_equ_size (c d : OwnedCfg) : owned_equ c d → c.pool.size = d.pool.size := fun E => by
  rw [owned_equ_eq E]

theorem terminal_proper : hproper terminal := fun c d E => by
  unfold terminal; rw [owned_equ_size c d E]

theorem hDone_proper (P : hprop) : hproper P → hproper (hDone P) := fun HP c d E =>
  and_congr (terminal_proper c d E) (HP c d E)

theorem hRet_proper (P : hprop) : hproper P → hproper (hRet owned_next P) := fun _ _ _ E => by
  rw [owned_equ_eq E]

theorem hNow_proper (P : hprop) : hproper P → hproper (hNow P) := fun HP c d E =>
  and_congr (not_congr (terminal_proper c d E)) (HP c d E)

theorem at_side_proper (i : Side) (P : hprop) : hproper P → hproper (at_side i P) :=
  fun HP c d E => HP _ _ (project_equ i c d E)

theorem view_pred_proper (P : hprop) : view_pred P → hproper P := fun HV c d E =>
  ⟨HV c d (owned_equ_same_view c d E),
   HV d c (owned_equ_same_view d c (owned_equ_Equivalence.symm E))⟩

/-- Heap/context/counter/observation/termination predicates are stable under selection, which
changes only the focus. -/
theorem view_selection_stable (P : hprop) : view_pred P → SelectionStable P := by
  intro HV d a d' TR K
  obtain ⟨Hh, -, Hc, Hb, Hn, Hl, Hs⟩ := owned_step_select_only _ _ _ TR K
  have Hv : same_view d d' :=
    ⟨fun _ => by rw [Hh]; exact peq_refl _, Hc.symm, Hb.symm, fun _ => by rw [Hn],
      fun _ => by rw [Hl], by rw [Hs]⟩
  exact ⟨HV _ _ Hv, HV _ _ (same_view_equivalence.symm Hv)⟩

theorem hTrue_proper : hproper hTrue := fun _ _ _ => Iff.rfl

-- Not ported: `lift_proper` (Ltac).

end CoCSL
