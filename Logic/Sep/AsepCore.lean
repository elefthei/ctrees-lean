/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.OwnedInterp

/-!
# Active separation: states, satisfaction and one-step composition

An `AsepState` pairs an owned configuration with the global world of the canonical runner and one
local world per lineage. `asep_sat I P Q` holds of the global runner when the child projection
satisfies `P`, the parent projection `Q`, on disjoint heap halves. The one-step rules
`asep_anc_compose`/`asep_enc_compose` and the coinductive `asep_agc_compose` show that each
global step advances exactly one lineage (← `CTree/Interp/CSL/Asep.v`, lines 1-805, plus the
remaining definitions of that file).
-/

@[expose] public section
namespace Tisl.CSL
open CTree Coinduction Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield Tisl.Notation
open ITree (Effect)

/-! ## Worlds, trees and state assertions -/

abbrev AsepWorld := World (writerE (CSLObs (Nat × Nat)))
abbrev AsepTree := ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)
abbrev AsepPred := AsepTree → AsepWorld → Prop
abbrev AsepRet := PUnit × SSig → AsepWorld → Prop

def state_sat (I : OwnedCfg → assn ManagedHeap) : OwnedCfg → Prop :=
  fun c => owned_wf c ∧ I c (joined_heap c)

def state_obligation (i : Side) (P : OwnedCfg → Prop) (c : OwnedCfg) : assn ManagedHeap :=
  fun h => h ≈ c.heap i ∧ P (project i c)

theorem state_split_iff (P Q : OwnedCfg → Prop) (c : OwnedCfg) :
    state_sat (fun d => asep (state_obligation .child P d) (state_obligation .parent Q d)) c ↔
      owned_wf c ∧ P (project .child c) ∧ Q (project .parent c) :=
  ⟨fun ⟨W, H⟩ => ⟨W, (asep_pinned _ _ _ _ W.2.2.2.2.2.2.2).1 H⟩,
   fun ⟨W, H⟩ => ⟨W, (asep_pinned _ _ _ _ W.2.2.2.2.2.2.2).2 H⟩⟩

/-- Rocq `Proper (owned_equ ==> iff)`; `owned_equ` is equality. -/
theorem state_split_proper (P Q : OwnedCfg → Prop)
    (_ : ∀ c d, owned_equ c d → (P c ↔ P d)) (_ : ∀ c d, owned_equ c d → (Q c ↔ Q d)) :
    ∀ c d, owned_equ c d →
      (state_sat (fun c => asep (state_obligation .child P c) (state_obligation .parent Q c)) c ↔
       state_sat (fun c => asep (state_obligation .child P c) (state_obligation .parent Q c)) d) :=
  fun _ _ E => owned_equ_eq E ▸ Iff.rfl

theorem state_split_forget (A B : assn ManagedHeap) (c : OwnedCfg) (_ : AProper A)
    (_ : AProper B)
    (HI : state_sat (fun d => asep
      (state_obligation .child (fun e => A (csl_memory (joined_state e))) d)
      (state_obligation .parent (fun e => B (csl_memory (joined_state e))) d)) c) :
    asep A B (csl_memory (joined_state c)) := by
  obtain ⟨W, HC, HP⟩ := (state_split_iff _ _ c).1 HI
  rw [owned_joined_state_project] at HC HP
  exact ⟨c.heap .child, c.heap .parent, W.2.2.2.2.2.2.2, peq_refl _, HC, HP⟩

/-! ## Active separation states -/

/-- Rocq `as_cfg`/`as_global`/`as_local`; `local` is a Lean keyword, so the last field is `loc`. -/
structure AsepState where
  cfg : OwnedCfg
  global : AsepWorld
  loc : Side → AsepWorld

def asep_state_ok (s : AsepState) : Prop :=
  active_erasable s.cfg ∧ NotDone s.global ∧ ∀ i, NotDone (s.loc i)

def asep_advance (s : AsepState) (a : OwnedAction) (d : OwnedCfg) : AsepState where
  cfg := d
  global := after_logs (action_logs a (joined_heap d)) s.global
  loc := fun i =>
    if side_eqb a.owner i then
      after_logs (action_logs (project_action i s.cfg a) (joined_heap (project i d))) (s.loc i)
    else s.loc i

def asep_step (s : AsepState) (a : OwnedAction) (s' : AsepState) : Prop :=
  owned_step s.cfg a s'.cfg ∧ s' = asep_advance s a s'.cfg

def asep_closed (I : AsepState → Prop) : Prop :=
  ∀ s a s', asep_state_ok s → I s → asep_step s a s' → I s'

def local_obligation (i : Side) (P : AsepPred) (s : AsepState) : assn ManagedHeap :=
  state_obligation i (fun c => P (owned_interp c) (s.loc i)) s.cfg

def asep_at (I : AsepState → Prop) (P Q : AsepPred) (s : AsepState) : Prop :=
  asep_state_ok s ∧ I s ∧
    asep (local_obligation .child P s) (local_obligation .parent Q s) (joined_heap s.cfg)

def asep_sat (I : AsepState → Prop) (P Q : AsepPred) : AsepPred :=
  fun t w => ∃ s, t ~ owned_interp s.cfg ∧ w = s.global ∧ asep_at I P Q s

def asep_pred_ok (P : AsepPred) : Prop :=
  (∀ t w, P t w → NotDone w) ∧ SbProper P

private theorem other_ne (i : Side) : i ≠ other i := by cases i <;> nofun

private theorem other_other (i : Side) : other (other i) = i := by cases i <;> rfl

private theorem asep_step_global {s s' : AsepState} {a : OwnedAction} (H : asep_step s a s') :
    s'.global = after_logs (action_logs a (joined_heap s'.cfg)) s.global :=
  congrArg AsepState.global H.2

private theorem asep_step_loc_own {s s' : AsepState} {a : OwnedAction} (H : asep_step s a s') :
    s'.loc a.owner = after_logs (action_logs (project_action a.owner s.cfg a)
      (joined_heap (project a.owner s'.cfg))) (s.loc a.owner) :=
  (congrArg (·.loc a.owner) H.2).trans (by simp [asep_advance])

private theorem asep_step_loc_foreign {s s' : AsepState} {a : OwnedAction} {i : Side}
    (H : asep_step s a s') (Ho : a.owner ≠ i) : s'.loc i = s.loc i :=
  (congrArg (·.loc i) H.2).trans (by simp [asep_advance, Ho])

theorem asep_state_ok_step (s : AsepState) (a : OwnedAction) (s' : AsepState)
    (Hok : asep_state_ok s) (Hst : asep_step s a s') : asep_state_ok s' := by
  obtain ⟨He, Hw, Hl⟩ := Hok
  refine ⟨active_erasable_step _ _ _ He Hst.1, (asep_step_global Hst) ▸ after_logs_not_done _ Hw,
    fun i => ?_⟩
  by_cases Ho : a.owner = i
  · subst Ho; rw [asep_step_loc_own Hst]; exact after_logs_not_done _ (Hl _)
  · rw [asep_step_loc_foreign Hst Ho]; exact Hl i

theorem asep_closed_true : asep_closed fun _ => True := fun _ _ _ _ _ _ => trivial

theorem local_obligation_proper (i : Side) (P : AsepPred) (s : AsepState) :
    AProper (local_obligation i P s) :=
  fun _ _ E ⟨Hpin, HP⟩ => ⟨peq_trans _ _ _ (peq_sym _ _ E) Hpin, HP⟩

theorem asep_local_pinned (s : AsepState) (P Q : AsepPred) (W : owned_wf s.cfg) :
    asep (local_obligation .child P s) (local_obligation .parent Q s) (joined_heap s.cfg) ↔
      P (owned_interp (project .child s.cfg)) (s.loc .child) ∧
      Q (owned_interp (project .parent s.cfg)) (s.loc .parent) :=
  asep_pinned _ _ _ _ W.2.2.2.2.2.2.2

theorem asep_at_intro (I : AsepState → Prop) (P Q : AsepPred) (s : AsepState)
    (Hok : asep_state_ok s) (HI : I s)
    (HC : P (owned_interp (project .child s.cfg)) (s.loc .child))
    (HP : Q (owned_interp (project .parent s.cfg)) (s.loc .parent)) : asep_at I P Q s :=
  ⟨Hok, HI, (asep_local_pinned s P Q Hok.1.1.1).2 ⟨HC, HP⟩⟩

theorem asep_at_inv (I : AsepState → Prop) (P Q : AsepPred) (s : AsepState)
    (H : asep_at I P Q s) :
    asep_state_ok s ∧ owned_wf s.cfg ∧ I s ∧
      P (owned_interp (project .child s.cfg)) (s.loc .child) ∧
      Q (owned_interp (project .parent s.cfg)) (s.loc .parent) :=
  ⟨H.1, H.1.1.1.1, H.2.1, (asep_local_pinned s P Q H.1.1.1.1).1 H.2.2⟩

theorem asep_sat_intro (I : AsepState → Prop) (P Q : AsepPred) (s : AsepState)
    (H : asep_at I P Q s) : asep_sat I P Q (owned_interp s.cfg) s.global :=
  ⟨s, sbisim_refl _, rfl, H⟩

theorem asep_sat_inv (I : AsepState → Prop) (P Q : AsepPred) (t : AsepTree) (w : AsepWorld)
    (H : asep_sat I P Q t w) :
    ∃ s, t ~ owned_interp s.cfg ∧ w = s.global ∧
      asep_state_ok s ∧ owned_wf s.cfg ∧ I s ∧
      P (owned_interp (project .child s.cfg)) (s.loc .child) ∧
      Q (owned_interp (project .parent s.cfg)) (s.loc .parent) :=
  let ⟨s, Et, Ew, H⟩ := H
  ⟨s, Et, Ew, asep_at_inv I P Q s H⟩

theorem asep_sat_pred_ok (I : AsepState → Prop) (P Q : AsepPred) :
    asep_pred_ok (asep_sat I P Q) :=
  ⟨fun _ _ ⟨_, _, Ew, Hok, _⟩ => Ew ▸ Hok.2.1,
   fun _ E => ⟨fun ⟨s, Et, Ew, H⟩ => ⟨s, sbisim_trans (sbisim_symm E) Et, Ew, H⟩,
     fun ⟨s, Et, Ew, H⟩ => ⟨s, sbisim_trans E Et, Ew, H⟩⟩⟩

theorem asep_sat_mono (I J : AsepState → Prop) (P P' Q Q' : AsepPred) (HI : ∀ s, I s → J s)
    (HP : ∀ t w, P t w → P' t w) (HQ : ∀ t w, Q t w → Q' t w) :
    ∀ t w, asep_sat I P Q t w → asep_sat J P' Q' t w := by
  intro t w H
  obtain ⟨s, Et, Ew, Hok, -, Hinv, HC, HPar⟩ := asep_sat_inv I P Q t w H
  exact ⟨s, Et, Ew, asep_at_intro J P' Q' s Hok (HI _ Hinv) (HP _ _ HC) (HQ _ _ HPar)⟩

theorem asep_pred_ok_entails {i : Option Type} (p : Ticl (writerE (CSLObs (Nat × Nat))) i) :
    asep_pred_ok (entails p) :=
  ⟨fun _ _ H => ticl_not_done p H, fun _ E => proper_entails_meq p E⟩

theorem asep_pred_transport (P : AsepPred) (HP : asep_pred_ok P) (t u : AsepTree)
    (w : AsepWorld) (E : t ~ u) (H : P t w) : P u w :=
  (HP.2 w E).1 H

theorem asep_pred_ok_anc (P Q : AsepPred) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q) :
    asep_pred_ok (anc P Q) :=
  ⟨fun _ _ H => HP.1 _ _ H.1, fun _ E =>
    proper_ax_equ (meq := sbisim Eq) (fun _ _ w h => HP.2 w h) (fun _ _ w h => HQ.2 w h) E⟩

theorem asep_pred_ok_enc (P Q : AsepPred) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q) :
    asep_pred_ok (enc P Q) :=
  ⟨fun _ _ H => HP.1 _ _ H.1, fun _ E =>
    proper_ex_equ (meq := sbisim Eq) (fun _ _ w h => HP.2 w h) (fun _ _ w h => HQ.2 w h) E⟩

theorem asep_pred_ok_agc (P : AsepPred) (HP : asep_pred_ok P) : asep_pred_ok (agc P) :=
  ⟨fun _ _ H => HP.1 _ _ (agc_unfold.1 H).1, fun _ E =>
    proper_ag_equ (meq := sbisim Eq) (fun _ _ w h => HP.2 w h) E⟩

/-! ## Silent prefixes and visible frontiers -/

def owner_visible (i : Side) (_c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  a.owner = i ∧ erase_action_label a (joined_heap c') ≠ none

def asep_silent (s s' : AsepState) : Prop :=
  ∃ a, asep_step s a s' ∧ erase_action_label a (joined_heap s'.cfg) = none

def asep_frontier (s s' : AsepState) : Prop :=
  ∃ mid a, Star asep_silent s mid ∧ asep_step mid a s' ∧
    erase_action_label a (joined_heap s'.cfg) ≠ none

theorem asep_silent_lift (s : AsepState) (d : OwnedCfg) (H : Star silent_next s.cfg d) :
    ∃ s', Star asep_silent s s' ∧ s'.cfg = d := by
  induction H with
  | refl => exact ⟨s, .refl, rfl⟩
  | tail _ hab ih =>
    obtain ⟨mid, Hmid, rfl⟩ := ih
    obtain ⟨a, Hs, Hl⟩ := hab
    exact ⟨asep_advance mid a _, Hmid.tail ⟨a, ⟨Hs, rfl⟩, Hl⟩, rfl⟩

theorem asep_silent_cfg (s s' : AsepState) (H : Star asep_silent s s') :
    Star silent_next s.cfg s'.cfg := by
  induction H with
  | refl => exact .refl
  | tail _ hab ih => obtain ⟨a, ⟨Hs, -⟩, Hl⟩ := hab; exact ih.tail ⟨a, Hs, Hl⟩

theorem asep_silent_worlds (s s' : AsepState) (H : Star asep_silent s s') :
    s'.global = s.global ∧ ∀ i, s'.loc i = s.loc i := by
  induction H with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | tail _ hab ih =>
    obtain ⟨a, Hst, Hl⟩ := hab
    refine ⟨(asep_step_global Hst).trans (by rw [action_logs_none _ _ Hl]; exact ih.1),
      fun i => ?_⟩
    by_cases Ho : a.owner = i
    · subst Ho
      rw [asep_step_loc_own Hst,
        action_logs_none _ _ ((owned_project_label_none _ _ _ _ _).2 Hl)]
      exact ih.2 _
    · exact (asep_step_loc_foreign Hst Ho).trans (ih.2 i)

theorem asep_closed_silent (I : AsepState → Prop) (s s' : AsepState) (Hclosed : asep_closed I)
    (Hok : asep_state_ok s) (HI : I s) (H : Star asep_silent s s') :
    asep_state_ok s' ∧ I s' := by
  induction H with
  | refl => exact ⟨Hok, HI⟩
  | tail _ hab ih =>
    obtain ⟨a, Hs, -⟩ := hab
    exact ⟨asep_state_ok_step _ a _ ih.1 Hs, Hclosed _ a _ ih.1 ih.2 Hs⟩

theorem asep_closed_frontier (I : AsepState → Prop) (s s' : AsepState) (Hclosed : asep_closed I)
    (Hok : asep_state_ok s) (HI : I s) (H : asep_frontier s s') : asep_state_ok s' ∧ I s' := by
  obtain ⟨mid, a, Hsil, Hs, -⟩ := H
  obtain ⟨Hokm, HIm⟩ := asep_closed_silent I s mid Hclosed Hok HI Hsil
  exact ⟨asep_state_ok_step _ a _ Hokm Hs, Hclosed _ a _ Hokm HIm Hs⟩

theorem asep_invisible (s : AsepState) (a : OwnedAction) (s' : AsepState) (i : Side)
    (Hok : asep_state_ok s) (Hst : asep_step s a s')
    (Hnot : ¬ owner_visible i s.cfg a s'.cfg) :
    owned_interp (project i s.cfg) ~ owned_interp (project i s'.cfg) ∧ s'.loc i = s.loc i := by
  by_cases Ho : a.owner = i
  · have Hnone : erase_action_label a (joined_heap s'.cfg) = none :=
      Classical.byContradiction fun h => Hnot ⟨Ho, h⟩
    subst Ho
    refine ⟨owned_silent_local _ _ _ Hok.1 (Star.single ⟨a, Hst.1, Hnone⟩), ?_⟩
    rw [asep_step_loc_own Hst,
      action_logs_none _ _ ((owned_project_label_none _ _ _ _ _).2 Hnone)]
    rfl
  · refine ⟨?_, asep_step_loc_foreign Hst Ho⟩
    rw [owned_equ_eq (owned_step_foreign i _ _ _ Hst.1 Ho)]
    exact sbisim_refl _

theorem asep_local_step_inv (s : AsepState) (a : OwnedAction) (s' : AsepState) (i : Side)
    (Hok : asep_state_ok s) (Hst : asep_step s a s') :
    (owned_interp (project i s.cfg) ~ owned_interp (project i s'.cfg) ∧ s'.loc i = s.loc i) ∨
      ∃ u, ktrans (owned_interp (project i s.cfg)) (s.loc i) u (s'.loc i) ∧
        u ~ owned_interp (project i s'.cfg) := by
  by_cases Ho : a.owner = i
  · rcases Hl : erase_action_label a (joined_heap s'.cfg) with _ | l
    · exact .inl (asep_invisible s a s' i Hok Hst fun ⟨_, H⟩ => H Hl)
    · obtain ⟨u, Hu, Eu⟩ := owned_owner_ktrans _ _ _ i (s.loc i) Hok.1 Hst.1 Ho
        (by rw [Hl]; nofun) (Hok.2.2 i)
      subst Ho
      exact .inr ⟨u, by rw [asep_step_loc_own Hst]; exact Hu, Eu⟩
  · exact .inl (asep_invisible s a s' i Hok Hst fun ⟨H, _⟩ => Ho H)

theorem asep_visible_forward_owner (s : AsepState) (t' : AsepTree) (w' : AsepWorld)
    (Hok : asep_state_ok s) (HT : ktrans (owned_interp s.cfg) s.global t' w')
    (Hw' : NotDone w') :
    ∃ s' u i, asep_frontier s s' ∧ t' ~ owned_interp s'.cfg ∧ w' = s'.global ∧
      ktrans (owned_interp (project i s.cfg)) (s.loc i) u (s'.loc i) ∧
      u ~ owned_interp (project i s'.cfg) ∧
      owned_interp (project (other i) s'.cfg) ~ owned_interp (project (other i) s.cfg) ∧
      s'.loc (other i) = s.loc (other i) := by
  have He := Hok.1
  have Hw := Hok.2.1
  obtain ⟨d, a, d', l, Hp, Hs, Hlabel, Et, Ew⟩ := owned_ktrans_forward _ _ _ _ He.1 Hw HT Hw'
  obtain ⟨mid, Hmid, rfl⟩ := asep_silent_lift s d Hp
  obtain ⟨Eg, El⟩ := asep_silent_worlds _ _ Hmid
  have Hokm := (asep_closed_silent _ _ _ asep_closed_true Hok trivial Hmid).1
  have Hst : asep_step mid a (asep_advance mid a d') := ⟨Hs, rfl⟩
  have Hvis : erase_action_label a (joined_heap d') ≠ none := by rw [Hlabel]; nofun
  obtain ⟨u, Hu, Eu⟩ := owned_owner_ktrans _ a d' a.owner (mid.loc a.owner) Hokm.1 Hs rfl Hvis
    (Hokm.2.2 _)
  have Hcfg := asep_silent_cfg _ _ Hmid
  rw [El] at Hu
  obtain ⟨v, Hv, Euv⟩ :=
    ktrans_semiproper (sbisim_symm (owned_silent_local _ _ a.owner He Hcfg)) Hu
  refine ⟨asep_advance mid a d', v, a.owner, ⟨mid, a, Hmid, Hst, Hvis⟩, Et,
    Ew.trans (congrArg _ Eg.symm), ?_, sbisim_trans (sbisim_symm Euv) Eu, ?_, ?_⟩
  · rw [asep_step_loc_own Hst, El]; exact Hv
  · exact sbisim_trans (owned_interp_equ _ _ (owned_step_foreign _ _ _ _ Hs (other_ne _)))
      (sbisim_symm (owned_silent_local _ _ _ He Hcfg))
  · exact (asep_step_loc_foreign Hst (other_ne _)).trans (El _)

theorem asep_local_lift (s : AsepState) (i : Side) (u : AsepTree) (v : AsepWorld)
    (Hok : asep_state_ok s) (Hready : owned_side_ready i s.cfg)
    (HT : ktrans (owned_interp (project i s.cfg)) (s.loc i) u v) (Hlive : NotDone v) :
    ∃ s' t' w', asep_frontier s s' ∧ owned_side_ready i s'.cfg ∧
      ktrans (owned_interp s.cfg) s.global t' w' ∧
      t' ~ owned_interp s'.cfg ∧ u ~ owned_interp (project i s'.cfg) ∧
      w' = s'.global ∧ v = s'.loc i ∧
      owned_interp (project (other i) s'.cfg) ~ owned_interp (project (other i) s.cfg) ∧
      s'.loc (other i) = s.loc (other i) := by
  obtain ⟨He, Hw, Hl⟩ := Hok
  obtain ⟨d, a, d', l, Hp, Hs, Hlabel, Eu, Ev⟩ :=
    owned_ktrans_forward _ _ _ _ (owned_active_local _ i He) (Hl i) HT Hlive
  obtain ⟨c, Hc, Hreadyc, Ec, Eforeign⟩ :=
    owned_local_silent_lift_cfg i _ _ Hp s.cfg (owned_equ_Equivalence.refl _) Hready
  obtain rfl := owned_equ_eq Ec
  obtain ⟨b, c', Hb, Ho, rfl, Ep⟩ := owned_step_lift i c a d' Hreadyc Hs
  obtain rfl := owned_equ_eq Ep
  have Hvis : erase_action_label b (joined_heap c') ≠ none := fun Hnone => by
    rw [(owned_project_label_none i c b (joined_heap c') _).2 Hnone] at Hlabel; cases Hlabel
  rcases Hlg : erase_action_label b (joined_heap c') with _ | lg
  · exact absurd Hlg Hvis
  obtain ⟨t', Ht', Et'⟩ := owned_interp_visible _ c b c' lg He.1 Hc Hb Hlg
  obtain ⟨mid, Hmid, rfl⟩ := asep_silent_lift s c Hc
  obtain ⟨Eg, El⟩ := asep_silent_worlds _ _ Hmid
  have Hst : asep_step mid b (asep_advance mid b c') := ⟨Hb, rfl⟩
  subst Ho
  refine ⟨asep_advance mid b c', t', (asep_advance mid b c').global, ⟨mid, b, Hmid, Hst, Hvis⟩,
    owned_side_ready_step _ _ b c' Hb rfl, ?_, Et', Eu, rfl, ?_, ?_, ?_⟩
  · show ktrans _ _ _ (after_logs _ mid.global)
    rw [Eg]; exact owned_label_ktrans b _ lg _ t' s.global Hlg Ht' Hw
  · rw [asep_step_loc_own Hst, El]; exact Ev
  · exact owned_interp_equ _ _ (owned_equ_Equivalence.trans
      (owned_step_foreign _ _ _ _ Hb (other_ne _)) Eforeign)
  · exact (asep_step_loc_foreign Hst (other_ne _)).trans (El _)

theorem asep_terminal_forward (s : AsepState) (t' : AsepTree) (w' : AsepWorld)
    (Hok : asep_state_ok s) (HT : ktrans (owned_interp s.cfg) s.global t' w')
    (Hnd : ¬ NotDone w') :
    ∃ s', Star asep_silent s s' ∧ s'.global = s.global ∧ (∀ i, s'.loc i = s.loc i) ∧
      s'.cfg.pool.size = 0 ∧ t' ~ (.stuck : AsepTree) ∧
      DoneWith (fun r predecessor => r = (PUnit.unit, joined_state s'.cfg) ∧
        predecessor = s.global) w' := by
  obtain ⟨d, Hp, Hz, Et, Hd⟩ := owned_ktrans_terminal _ _ _ _ Hok.1.1 HT Hnd
  obtain ⟨s', Hsil, rfl⟩ := asep_silent_lift s d Hp
  obtain ⟨Eg, El⟩ := asep_silent_worlds _ _ Hsil
  exact ⟨s', Hsil, Eg, El, Hz, Et, Hd⟩

theorem asep_auc_live (P R : AsepPred) (HP : asep_pred_ok P) (HR : asep_pred_ok R) :
    ∀ t w, Auc P R t w → NotDone w
  | _, _, .matchA h => HR.1 _ _ h
  | _, _, .stepA h _ _ => HP.1 _ _ h

theorem asep_euc_live (P R : AsepPred) (HP : asep_pred_ok P) (HR : asep_pred_ok R) :
    ∀ t w, Euc P R t w → NotDone w
  | _, _, .matchE h => HR.1 _ _ h
  | _, _, .stepE _ _ h _ _ => HP.1 _ _ h

theorem asep_pred_ok_auc (P R : AsepPred) (HP : asep_pred_ok P) (HR : asep_pred_ok R) :
    asep_pred_ok (Auc P R) :=
  ⟨asep_auc_live P R HP HR, fun _ E =>
    proper_au_equ (meq := sbisim Eq) (fun _ _ w h => HP.2 w h) (fun _ _ w h => HR.2 w h) E⟩

theorem asep_pred_ok_euc (P R : AsepPred) (HP : asep_pred_ok P) (HR : asep_pred_ok R) :
    asep_pred_ok (Euc P R) :=
  ⟨asep_euc_live P R HP HR, fun _ E =>
    proper_eu_equ (meq := sbisim Eq) (fun _ _ w h => HP.2 w h) (fun _ _ w h => HR.2 w h) E⟩

/-! ## Progress -/

theorem asep_can_step_frontier (c : OwnedCfg) (w : AsepWorld) (He : erasable c)
    (H : can_step (owned_interp c) w) :
    (∃ u v, ktrans (owned_interp c) w u v ∧ NotDone v) ∨
      ∃ d, Star silent_next c d ∧ d.pool.size = 0 := by
  obtain ⟨u, v, HT⟩ := H
  by_cases Hv : NotDone v
  · exact .inl ⟨u, v, HT, Hv⟩
  · obtain ⟨d, Hp, Hz, -⟩ := owned_ktrans_terminal c w u v He HT Hv
    exact .inr ⟨d, Hp, Hz⟩

theorem asep_local_terminal_lift (s : AsepState) (i : Side) (d : OwnedCfg)
    (Hr : owned_side_ready i s.cfg) (Hp : Star silent_next (project i s.cfg) d)
    (H0 : d.pool.size = 0) :
    ∃ s', Star asep_silent s s' ∧ s'.global = s.global ∧ (∀ j, s'.loc j = s.loc j) ∧
      (project i s'.cfg).pool.size = 0 ∧ s'.cfg.pool.focus = none ∧
      owned_equ (project (other i) s'.cfg) (project (other i) s.cfg) := by
  obtain ⟨c, Hc, Hready, Ec, Eforeign⟩ :=
    owned_local_silent_lift_cfg i _ _ Hp s.cfg (owned_equ_Equivalence.refl _) Hr
  obtain rfl := owned_equ_eq Ec
  obtain ⟨s', Hsil, rfl⟩ := asep_silent_lift s c Hc
  obtain ⟨Eg, El⟩ := asep_silent_worlds _ _ Hsil
  exact ⟨s', Hsil, Eg, El, H0, owned_side_ready_empty i _ Hready H0, Eforeign⟩

/-- A returning tree in a live world reaches a terminal world. -/
private theorem ret_ktrans_dead (x : PUnit × SSig) (w : AsepWorld) (Hw : NotDone w) :
    ∃ t' w', ktrans (pure x : AsepTree) w t' w' ∧ ¬ NotDone w' := by
  cases Hw with
  | pure => exact ⟨_, _, ktrans_done.2 ⟨rfl, rfl⟩, nofun⟩
  | obs e v => exact ⟨_, _, ktrans_finish.2 ⟨rfl, rfl⟩, nofun⟩

theorem asep_empty_can_step (c : OwnedCfg) (w : AsepWorld) (He : erasable c) (Hw : NotDone w)
    (H0 : c.pool.size = 0) : can_step (owned_interp c) w := by
  rw [proper_can_step (meq := sbisim Eq) (owned_interp_terminal c He H0)]
  obtain ⟨t', w', H, -⟩ := ret_ktrans_dead _ w Hw
  exact ⟨t', w', H⟩

theorem asep_progress_ready (s : AsepState) (i : Side) (Hok : asep_state_ok s)
    (Hr : owned_side_ready i s.cfg)
    (Hi : can_step (owned_interp (project i s.cfg)) (s.loc i))
    (Ho : can_step (owned_interp (project (other i) s.cfg)) (s.loc (other i))) :
    can_step (owned_interp s.cfg) s.global := by
  have He := Hok.1
  rcases asep_can_step_frontier _ _ (owned_active_local _ i He) Hi with
    ⟨u, v, HT, Hlive⟩ | ⟨d, Hp, H0⟩
  · obtain ⟨_, t', w', -, -, Ht, -⟩ := asep_local_lift s i u v Hok Hr HT Hlive
    exact ⟨t', w', Ht⟩
  obtain ⟨mid, Hsil, Eg, El, Hempty, Hfocus, Eforeign⟩ := asep_local_terminal_lift s i d Hr Hp H0
  rw [proper_can_step (meq := sbisim Eq) (owned_interp_silent _ _ He.1 (asep_silent_cfg _ _ Hsil)),
    ← Eg]
  have Hokm := (asep_closed_silent _ _ _ asep_closed_true Hok trivial Hsil).1
  have Hother : can_step (owned_interp (project (other i) mid.cfg)) (mid.loc (other i)) := by
    rw [owned_equ_eq Eforeign, El]; exact Ho
  rcases asep_can_step_frontier _ _ (owned_active_local _ (other i) Hokm.1) Hother with
    ⟨u, v, HT, Hlive⟩ | ⟨d', Hp', H0'⟩
  · obtain ⟨_, t', w', -, -, Ht, -⟩ := asep_local_lift mid (other i) u v Hokm (.inl Hfocus) HT Hlive
    exact ⟨t', w', Ht⟩
  obtain ⟨s', Hsil', Eg', -, Hempty', -, Eforeign'⟩ :=
    asep_local_terminal_lift mid (other i) d' (.inl Hfocus) Hp' H0'
  rw [proper_can_step (meq := sbisim Eq)
    (owned_interp_silent _ _ Hokm.1.1 (asep_silent_cfg _ _ Hsil')), ← Eg']
  have Hok' := (asep_closed_silent _ _ _ asep_closed_true Hokm trivial Hsil').1
  refine asep_empty_can_step _ _ Hok'.1.1 Hok'.2.1 ?_
  have Hi' : (project i s'.cfg).pool.size = 0 := by
    rw [other_other] at Eforeign'; rw [owned_equ_eq Eforeign']
    exact Hempty
  exact projected_both_empty _ i Hi' Hempty'

theorem asep_progress (s : AsepState) (Hok : asep_state_ok s)
    (HC : can_step (owned_interp (project .child s.cfg)) (s.loc .child))
    (HP : can_step (owned_interp (project .parent s.cfg)) (s.loc .parent)) :
    can_step (owned_interp s.cfg) s.global := by
  obtain ⟨i, Hr⟩ : ∃ i, owned_side_ready i s.cfg := by
    rcases Hf : s.cfg.pool.focus with _ | j
    · exact ⟨.child, .inl Hf⟩
    · exact ⟨_, .inr ⟨j, Hf, rfl⟩⟩
  cases i
  · exact asep_progress_ready s .child Hok Hr HC HP
  · exact asep_progress_ready s .parent Hok Hr HP HC

/-! ## One-step composition -/

theorem asep_anc_live (s : AsepState) (i : Side) (P R : AsepPred) (u : AsepTree) (v : AsepWorld)
    (Hok : asep_state_ok s) (HC : anc P R (owned_interp (project i s.cfg)) (s.loc i))
    (HR : ∀ t w, R t w → NotDone w) (HT : ktrans (owned_interp s.cfg) s.global u v) :
    NotDone v := by
  refine Classical.byContradiction fun Hdead => ?_
  obtain ⟨s', Hsil, -, -, Hempty, -⟩ := asep_terminal_forward s u v Hok HT Hdead
  have Hok' := (asep_closed_silent _ _ _ asep_closed_true Hok trivial Hsil).1
  have E : owned_interp (project i s.cfg) ~
      (pure (PUnit.unit, joined_state (project i s'.cfg)) : AsepTree) :=
    sbisim_trans (owned_silent_local _ _ i Hok.1 (asep_silent_cfg _ _ Hsil))
      (owned_interp_terminal _ (owned_active_local _ i Hok'.1)
        (project_size_terminal i _ Hempty))
  obtain ⟨t', w', Ht, Hdead'⟩ := ret_ktrans_dead _ _ (Hok.2.2 i)
  obtain ⟨q, Hq, -⟩ := ktrans_semiproper (sbisim_symm E) Ht
  exact Hdead' (HR q w' (HC.2.2 q w' Hq))

theorem asep_anc_compose (I : AsepState → Prop) (P P' Q Q' : AsepPred) (t : AsepTree)
    (w : AsepWorld) (Hclosed : asep_closed I) (HP : asep_pred_ok P) (HP' : asep_pred_ok P')
    (HQ : asep_pred_ok Q) (HQ' : asep_pred_ok Q') (H : asep_sat I (anc P P') (anc Q Q') t w) :
    anc (asep_sat I P Q) (fun u v => asep_sat I P' Q u v ∨ asep_sat I P Q' u v) t w := by
  obtain ⟨s, Et, rfl, Hok, -, HI, HC, HPar⟩ := asep_sat_inv I _ _ t w H
  refine ⟨⟨s, Et, rfl, asep_at_intro I P Q s Hok HI HC.1 HPar.1⟩,
    (proper_can_step (meq := sbisim Eq) Et).2 (asep_progress s Hok HC.2.1 HPar.2.1),
    fun u v HT => ?_⟩
  obtain ⟨q, Hq, Eu⟩ := ktrans_semiproper Et HT
  have Hv := asep_anc_live s .child P P' q v Hok HC HP'.1 Hq
  obtain ⟨s', r, i, Hfront, Eq, rfl, Hlocal, Er, Ef, Ew⟩ :=
    asep_visible_forward_owner s q v Hok Hq Hv
  obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
  have Eus := sbisim_trans Eu Eq
  cases i <;> simp only [other] at Ef Ew
  · refine .inl ⟨s', Eus, rfl, asep_at_intro I P' Q s' Hok' HI' ?_ ?_⟩
    · exact asep_pred_transport P' HP' _ _ _ Er (HC.2.2 _ _ Hlocal)
    · rw [Ew]; exact asep_pred_transport Q HQ _ _ _ (sbisim_symm Ef) HPar.1
  · refine .inr ⟨s', Eus, rfl, asep_at_intro I P Q' s' Hok' HI' ?_ ?_⟩
    · rw [Ew]; exact asep_pred_transport P HP _ _ _ (sbisim_symm Ef) HC.1
    · exact asep_pred_transport Q' HQ' _ _ _ Er (HPar.2.2 _ _ Hlocal)

theorem asep_enc_ready (s : AsepState) (i : Side) (P R : AsepPred) (Hok : asep_state_ok s)
    (Hready : owned_side_ready i s.cfg) (HR : asep_pred_ok R)
    (H : enc P R (owned_interp (project i s.cfg)) (s.loc i)) :
    ∃ s' q, asep_frontier s s' ∧ ktrans (owned_interp s.cfg) s.global q s'.global ∧
      q ~ owned_interp s'.cfg ∧ R (owned_interp (project i s'.cfg)) (s'.loc i) ∧
      owned_interp (project (other i) s'.cfg) ~ owned_interp (project (other i) s.cfg) ∧
      s'.loc (other i) = s.loc (other i) := by
  obtain ⟨-, r, v, HT, Hpost⟩ := H
  obtain ⟨s', q, w', Hfront, -, Hq, Eq, Er, rfl, rfl, Ef, El⟩ :=
    asep_local_lift s i r v Hok Hready HT (HR.1 _ _ Hpost)
  exact ⟨s', q, Hfront, Hq, Eq, asep_pred_transport R HR _ _ _ Er Hpost, Ef, El⟩

theorem asep_enc_compose (I : AsepState → Prop) (P P' Q Q' : AsepPred) (t : AsepTree)
    (w : AsepWorld) (Hclosed : asep_closed I) (HP : asep_pred_ok P) (HP' : asep_pred_ok P')
    (HQ : asep_pred_ok Q) (HQ' : asep_pred_ok Q') (H : asep_sat I (enc P P') (enc Q Q') t w) :
    enc (asep_sat I P Q) (fun u v => asep_sat I P' Q u v ∨ asep_sat I P Q' u v) t w := by
  obtain ⟨s, Et, rfl, Hok, -, HI, HC, HPar⟩ := asep_sat_inv I _ _ t w H
  refine ⟨⟨s, Et, rfl, asep_at_intro I P Q s Hok HI HC.1 HPar.1⟩, ?_⟩
  obtain ⟨i, Hready⟩ : ∃ i, owned_side_ready i s.cfg := by
    rcases Hf : s.cfg.pool.focus with _ | j
    · exact ⟨.child, .inl Hf⟩
    · exact ⟨_, .inr ⟨j, Hf, rfl⟩⟩
  cases i
  · obtain ⟨s', q, Hfront, HT, Eq, Hpost, Ef, Ew⟩ :=
      asep_enc_ready s .child P P' Hok Hready HP' HC
    obtain ⟨r, HTr, Er⟩ := ktrans_semiproper (sbisim_symm Et) HT
    obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
    simp only [other] at Ef Ew
    refine ⟨r, s'.global, HTr, .inl ⟨s', sbisim_trans (sbisim_symm Er) Eq, rfl,
      asep_at_intro I P' Q s' Hok' HI' Hpost ?_⟩⟩
    rw [Ew]; exact asep_pred_transport Q HQ _ _ _ (sbisim_symm Ef) HPar.1
  · obtain ⟨s', q, Hfront, HT, Eq, Hpost, Ef, Ew⟩ :=
      asep_enc_ready s .parent Q Q' Hok Hready HQ' HPar
    obtain ⟨r, HTr, Er⟩ := ktrans_semiproper (sbisim_symm Et) HT
    obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
    simp only [other] at Ef Ew
    refine ⟨r, s'.global, HTr, .inr ⟨s', sbisim_trans (sbisim_symm Er) Eq, rfl,
      asep_at_intro I P Q' s' Hok' HI' ?_ Hpost⟩⟩
    rw [Ew]; exact asep_pred_transport P HP _ _ _ (sbisim_symm Ef) HC.1

/-- Next with a true guard still advances only one lineage on the shared run. -/
theorem asep_ax_compose (I : AsepState → Prop) (P Q : AsepPred) (t : AsepTree) (w : AsepWorld)
    (Hclosed : asep_closed I) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q)
    (H : asep_sat I (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) P)
      (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) Q) t w) :
    anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun u v => asep_sat I P (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) u v ∨
        asep_sat I (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) Q u v) t w := by
  obtain ⟨-, Hcan, Hnext⟩ := asep_anc_compose I _ P _ Q t w Hclosed
    (asep_pred_ok_entails _) HP (asep_pred_ok_entails _) HQ H
  exact ⟨⟨trivial, can_step_not_done Hcan⟩, Hcan, Hnext⟩

theorem asep_ex_compose (I : AsepState → Prop) (P Q : AsepPred) (t : AsepTree) (w : AsepWorld)
    (Hclosed : asep_closed I) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q)
    (H : asep_sat I (enc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) P)
      (enc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) Q) t w) :
    enc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun u v => asep_sat I P (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) u v ∨
        asep_sat I (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) Q u v) t w := by
  obtain ⟨-, u, v, HT, Hnext⟩ := asep_enc_compose I _ P _ Q t w Hclosed
    (asep_pred_ok_entails _) HP (asep_pred_ok_entails _) HQ H
  exact ⟨⟨trivial, ktrans_not_done HT⟩, u, v, HT, Hnext⟩

theorem asep_agc_compose (I : AsepState → Prop) (P Q : AsepPred) (t : AsepTree) (w : AsepWorld)
    (Hclosed : asep_closed I) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q)
    (H : asep_sat I (agc P) (agc Q) t w) : agc (asep_sat I P Q) t w := by
  refine coinduction (b := agcF (asep_sat I P Q))
    (fun p : (Σ' t w, asep_sat I (agc P) (agc Q) t w) => p.1) (fun p => p.2.1)
    (fun R _ CIH => ?_) ⟨t, w, H⟩
  rintro ⟨t, w, H⟩
  obtain ⟨s, Et, rfl, Hok, -, HI, HC, HPar⟩ := asep_sat_inv I _ _ t w H
  have HCstep := agc_unfold.1 HC
  have HPstep := agc_unfold.1 HPar
  obtain ⟨Hnow, Hcan, -⟩ := asep_anc_compose I P (agc P) Q (agc Q) t s.global Hclosed HP
    (asep_pred_ok_agc P HP) HQ (asep_pred_ok_agc Q HQ)
    ⟨s, Et, rfl, asep_at_intro I _ _ s Hok HI HCstep HPstep⟩
  refine ⟨Hnow, Hcan, fun u v HT => ?_⟩
  obtain ⟨q, Hq, Eu⟩ := ktrans_semiproper Et HT
  have Hlive := asep_anc_live s .child P (agc P) q v Hok HCstep (asep_pred_ok_agc P HP).1 Hq
  obtain ⟨s', r, i, Hfront, Eq, rfl, HTi, Er, Ef, Ew⟩ :=
    asep_visible_forward_owner s q v Hok Hq Hlive
  obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
  refine CIH ⟨u, s'.global, s', sbisim_trans Eu Eq, rfl, ?_⟩
  cases i <;> simp only [other] at Ef Ew
  · refine asep_at_intro I _ _ s' Hok' HI' ?_ ?_
    · exact asep_pred_transport _ (asep_pred_ok_agc P HP) _ _ _ Er (HCstep.2.2 _ _ HTi)
    · rw [Ew]; exact asep_pred_transport _ (asep_pred_ok_agc Q HQ) _ _ _ (sbisim_symm Ef) HPar
  · refine asep_at_intro I _ _ s' Hok' HI' ?_ ?_
    · rw [Ew]; exact asep_pred_transport _ (asep_pred_ok_agc P HP) _ _ _ (sbisim_symm Ef) HC
    · exact asep_pred_transport _ (asep_pred_ok_agc Q HQ) _ _ _ Er (HPstep.2.2 _ _ HTi)

/-! ## Definitions used by the return and until rules (`Logic/Sep/Asep.lean`) -/

def asep_ret (I : AsepState → Prop) (RC RP : AsepRet) : AsepRet :=
  fun r w => ∃ s,
    asep_state_ok s ∧ I s ∧ s.cfg.pool.size = 0 ∧
    owned_result_rel (PUnit.unit, joined_state s.cfg) r ∧ w = s.global ∧
    asep
      (state_obligation .child
        (fun c => RC (PUnit.unit, joined_state c) (s.loc .child)) s.cfg)
      (state_obligation .parent
        (fun c => RP (PUnit.unit, joined_state c) (s.loc .parent)) s.cfg)
      (joined_heap s.cfg)

def asep_until_guard (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet) : AsepPred :=
  fun t w =>
    asep_sat I P Q t w ∨
    asep_sat I (entails (Ticl.ret (E := writerE (CSLObs (Nat × Nat))) RC)) Q t w ∨
    asep_sat I P (entails (Ticl.ret (E := writerE (CSLObs (Nat × Nat))) RP)) t w

/-- Finite existential-until ranks count retained local raw transitions. -/
def asep_euc_rank (P R : AsepPred) : Nat → AsepPred
  | 0 => R
  | k + 1 => enc P (asep_euc_rank P R k)

end Tisl.CSL
