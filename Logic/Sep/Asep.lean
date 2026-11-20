/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.AsepCore

/-!
# Active separation: native return, until and fair existential always

Native returns of both lineages compose into a joint return (`asep_ret_compose`); universal and
existential until over native returns compose by induction on both local derivations
(`asep_auc_ret_compose`) or on finite existential ranks (`asep_euc_ret_compose`); one valid
execution with infinitely many visible actions of each lineage gives existential always
(`asep_egc_run`) (← `CTree/Interp/CSL/Asep.v`, lines 806-1572).
-/

@[expose] public section
namespace Tisl.CSL
open CTree Coinduction Notation Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield
open ITree (Effect)

/-- Native return of a canonical-runner tree (Rocq `entails (SSig * unit) true (CRet R)`). -/
local notation "retP " R => (entails (Ticl.ret R) : AsepPred)

/-! ## Native return -/

theorem asep_ret_elim (I : AsepState → Prop) (RC RP : AsepRet) (st : SSig) (w : AsepWorld) :
    asep_ret I RC RP (⟨⟩, st) w → ∃ s,
      asep_state_ok s ∧ I s ∧ s.cfg.pool.size = 0 ∧ owned_wf s.cfg ∧ st = joined_state s.cfg ∧
      w = s.global ∧ RC (⟨⟩, local_state .child s.cfg) (s.loc .child) ∧
      RP (⟨⟩, local_state .parent s.cfg) (s.loc .parent) := by
  rintro ⟨s, Hok, HI, Ht, Hresult, Hw, Hsep⟩
  have Hwf : owned_wf s.cfg := Hok.1.1.1
  obtain ⟨HC, HP⟩ := (asep_pinned _ _ _ _ Hwf.2.2.2.2.2.2.2).1 Hsep
  rw [owned_joined_state_project] at HC HP
  obtain ⟨-, Ex, Eh⟩ := Hresult
  exact ⟨s, Hok, HI, Ht, Hwf, Prod.ext (managed_heap_ext _ _ Eh).symm Ex.symm, Hw, HC, HP⟩

theorem asep_ret_no_live (R : AsepRet) (t : AsepTree) (w : AsepWorld) (u : AsepTree)
    (v : AsepWorld) : (retP R) t w → ktrans t w u v → ¬ NotDone v := by
  rintro ⟨x, -, -, -, Hnext⟩ HT Hv
  cases Hnext u v HT <;> cases Hv

theorem asep_at_auc_ret_step (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet)
    (s : AsepState) (a : OwnedAction) (s' : AsepState) (Hclosed : asep_closed I)
    (HP : asep_pred_ok P) (HQ : asep_pred_ok Q)
    (H : asep_at I (Auc P (retP RC)) (Auc Q (retP RP)) s) (Hstep : asep_step s a s') :
    asep_at I (Auc P (retP RC)) (Auc Q (retP RP)) s' := by
  obtain ⟨Hok, -, HI, HC, HPar⟩ := asep_at_inv I _ _ s H
  have Hok' := asep_state_ok_step s a s' Hok Hstep
  have Hlocal : ∀ i (A : AsepPred) (R : AsepRet), asep_pred_ok A →
      Auc A (retP R) (owned_interp (project i s.cfg)) (s.loc i) →
      Auc A (retP R) (owned_interp (project i s'.cfg)) (s'.loc i) := by
    intro i A R HA HU
    have HAU := asep_pred_ok_auc A _ HA (asep_pred_ok_entails (Ticl.ret R))
    rcases asep_local_step_inv s a s' i Hok Hstep with ⟨Et, Ew⟩ | ⟨u, HT, Eu⟩
    · rw [Ew]; exact asep_pred_transport _ HAU _ _ _ Et HU
    · cases HU with
      | matchA HR => exact absurd (Hok'.2.2 i) (asep_ret_no_live _ _ _ _ _ HR HT)
      | stepA _ _ Hnext => exact asep_pred_transport _ HAU _ _ _ Eu (Hnext _ _ HT)
  exact asep_at_intro I _ _ s' Hok' (Hclosed s a s' Hok HI Hstep) (Hlocal .child P RC HP HC)
    (Hlocal .parent Q RP HQ HPar)

theorem asep_auc_ret_empty (c : OwnedCfg) (P : AsepPred) (R : AsepRet) (w : AsepWorld)
    (He : erasable c) (H0 : c.pool.size = 0) (HP : asep_pred_ok P)
    (HU : Auc P (retP R) (owned_interp c) w) : (retP R) (owned_interp c) w := by
  cases HU with
  | matchA HR => exact HR
  | stepA HG Hcan Hnext =>
    obtain ⟨u, v, HT⟩ := Hcan
    have Hret : (retP fun _ _ => True) (owned_interp c) w :=
      (proper_entails_meq _ (owned_interp_terminal c He H0)).2 (ret_ret (HP.1 _ _ HG) trivial)
    exact (asep_ret_no_live _ _ _ _ _ Hret HT
      (asep_auc_live P _ HP (asep_pred_ok_entails (Ticl.ret R)) u v (Hnext u v HT))).elim

theorem asep_ret_local_frontier (c : OwnedCfg) (R : AsepRet) (w : AsepWorld) (He : erasable c)
    (HR : (retP R) (owned_interp c) w) : ∃ d, Star silent_next c d ∧ d.pool.size = 0 := by
  have ⟨_, _, _, Hcan, _⟩ := HR
  rcases asep_can_step_frontier c w He Hcan with ⟨u, v, HT, Hv⟩ | Hdone
  · exact absurd Hv (asep_ret_no_live _ _ _ _ _ HR HT)
  · exact Hdone

theorem asep_ret_value (R : AsepRet) (x : PUnit × SSig) (w : AsepWorld)
    (H : (retP R) (pure x : AsepTree) w) : R x w := by
  obtain ⟨r, HR, -, ⟨u, v, HT⟩, Hall⟩ := H
  have Hd : done_eq r v := by cases Hall u v HT <;> constructor <;> rfl
  cases val_eq_inv (trans_ret_inv (ktrans_done_eq_inv HT Hd).1).2
  exact HR

theorem asep_ret_empty (c : OwnedCfg) (R : AsepRet) (w : AsepWorld) (He : erasable c)
    (H0 : c.pool.size = 0) (HR : (retP R) (owned_interp c) w) : R (⟨⟩, joined_state c) w :=
  asep_ret_value R _ w ((proper_entails_meq _ (owned_interp_terminal c He H0)).1 HR)

theorem asep_ret_unfocused_empty (c : OwnedCfg) (R : AsepRet) (w : AsepWorld) (He : erasable c)
    (Hf : c.pool.focus = none) (HR : (retP R) (owned_interp c) w) : c.pool.size = 0 := by
  obtain ⟨d, Hp, H0⟩ := asep_ret_local_frontier c R w He HR
  rw [owned_silent_unfocused c d Hp Hf]; exact H0

/-- Both native returns reach a terminal configuration through erased-silent actions. -/
theorem asep_ret_frontier (s : AsepState) (RC RP : AsepRet) (Hok : asep_state_ok s)
    (Hpair : (retP RC) (owned_interp (project .child s.cfg)) (s.loc .child) ∧
      (retP RP) (owned_interp (project .parent s.cfg)) (s.loc .parent)) :
    ∃ s', Star asep_silent s s' ∧ s'.global = s.global ∧ (∀ i, s'.loc i = s.loc i) ∧
      s'.cfg.pool.size = 0 ∧
      owned_interp s.cfg ~ (pure (⟨⟩, joined_state s'.cfg) : AsepTree) ∧
      RC (⟨⟩, local_state .child s'.cfg) (s'.loc .child) ∧
      RP (⟨⟩, local_state .parent s'.cfg) (s'.loc .parent) := by
  have He := Hok.1
  let R : Side → AsepRet := fun | .child => RC | .parent => RP
  have Hlocal : ∀ i, (retP (R i)) (owned_interp (project i s.cfg)) (s.loc i) := by
    intro i; cases i
    · exact Hpair.1
    · exact Hpair.2
  have Hend : ∃ s', Star asep_silent s s' ∧ s'.cfg.pool.size = 0 := by
    rcases Hfocus : s.cfg.pool.focus with _ | j
    · have Hempty : ∀ i, (project i s.cfg).pool.size = 0 := fun i =>
        asep_ret_unfocused_empty _ (R i) _ (owned_active_local _ i He)
          (project_focus_none i _ Hfocus) (Hlocal i)
      exact ⟨s, .refl, projected_both_empty _ .child (Hempty _) (Hempty _)⟩
    · generalize Hi : s.cfg.pool.tags[j] = i
      have Hr : owned_side_ready i s.cfg := .inr ⟨j, Hfocus, Hi⟩
      have Hfo : (project (other i) s.cfg).pool.focus = none :=
        project_focus_foreign (other i) s.cfg.pool j Hfocus (by rw [Hi]; cases i <;> decide)
      have Ho : (project (other i) s.cfg).pool.size = 0 :=
        asep_ret_unfocused_empty _ (R (other i)) _ (owned_active_local _ _ He) Hfo (Hlocal _)
      obtain ⟨d, Hp, H0⟩ :=
        asep_ret_local_frontier _ (R i) _ (owned_active_local _ i He) (Hlocal i)
      obtain ⟨s', Hsil, -, -, Hempty, -, Eother⟩ := asep_local_terminal_lift s i d Hr Hp H0
      rw [← owned_equ_eq Eother] at Ho
      exact ⟨s', Hsil, projected_both_empty _ i Hempty Ho⟩
  obtain ⟨s', Hsil, Hempty⟩ := Hend
  have Hcfg := asep_silent_cfg _ _ Hsil
  obtain ⟨Eg, El⟩ := asep_silent_worlds _ _ Hsil
  have Hok' := (asep_closed_silent _ _ _ asep_closed_true Hok trivial Hsil).1
  have He' := Hok'.1
  refine ⟨s', Hsil, Eg, El, Hempty,
    sbisim_trans (owned_interp_silent _ _ He.1 Hcfg) (owned_interp_terminal _ He'.1 Hempty), ?_⟩
  have Hpost : ∀ i, R i (⟨⟩, local_state i s'.cfg) (s'.loc i) := by
    intro i
    rw [← owned_joined_state_project]
    refine asep_ret_empty _ _ _ (owned_active_local _ i He') (project_size_terminal _ _ Hempty) ?_
    rw [El]
    exact (proper_entails_meq _ (owned_silent_local _ _ i He Hcfg)).1 (Hlocal i)
  exact ⟨Hpost .child, Hpost .parent⟩

/-- Native returns of both lineages compose into a joint native return. -/
theorem asep_ret_compose (I : AsepState → Prop) (RC RP : AsepRet) (t : AsepTree) (w : AsepWorld)
    (Hclosed : asep_closed I) (H : asep_sat I (retP RC) (retP RP) t w) :
    (retP (asep_ret I RC RP)) t w := by
  obtain ⟨s, Et, rfl, Hok, -, HI, HC, HP⟩ := asep_sat_inv I _ _ t w H
  obtain ⟨s', Hsil, Eg, -, H0, Eret, HC', HP'⟩ := asep_ret_frontier s RC RP Hok ⟨HC, HP⟩
  obtain ⟨Hok', HI'⟩ := asep_closed_silent I s s' Hclosed Hok HI Hsil
  refine (proper_entails_meq _ (sbisim_trans Et Eret)).2 (ret_ret Hok.2.1 ?_)
  refine ⟨s', Hok', HI', H0, ⟨rfl, rfl, peq_refl _⟩, Eg.symm, ?_⟩
  rw [← owned_joined_state_project] at HC' HP'
  exact (asep_pinned _ _ _ _ Hok'.1.1.1.2.2.2.2.2.2.2).2 ⟨HC', HP'⟩

theorem asep_until_guard_proper (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet) :
    SbProper (asep_until_guard I P Q RC RP) := fun w E =>
  or_congr ((asep_sat_pred_ok I P Q).2 w E)
    (or_congr ((asep_sat_pred_ok I _ Q).2 w E) ((asep_sat_pred_ok I P _).2 w E))

theorem asep_until_au_proper (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet) :
    SbProper (Auc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP))) := fun _ E =>
  proper_au_equ (meq := sbisim Eq) (fun _ _ w h => asep_until_guard_proper I P Q RC RP w h)
    (fun _ _ w h => (asep_pred_ok_entails (Ticl.ret (asep_ret I RC RP))).2 w h) E

theorem asep_until_eu_proper (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet) :
    SbProper (Euc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP))) := fun _ E =>
  proper_eu_equ (meq := sbisim Eq) (fun _ _ w h => asep_until_guard_proper I P Q RC RP w h)
    (fun _ _ w h => (asep_pred_ok_entails (Ticl.ret (asep_ret I RC RP))).2 w h) E

theorem asep_ret_can_step (R : AsepRet) (t : AsepTree) (w : AsepWorld)
    (H : (retP R) t w) : can_step t w :=
  have ⟨_, _, _, Hcan, _⟩ := H; Hcan

theorem asep_until_guard_live (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet)
    (t : AsepTree) (w : AsepWorld) (H : asep_until_guard I P Q RC RP t w) : NotDone w := by
  rcases H with H | H | H <;> exact (asep_sat_pred_ok _ _ _).1 _ _ H

/-- The nested inductions decrease the Child and Parent AU derivations. Their current views
carry the ordinary invariant through each frontier. -/
theorem asep_until_auc (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet)
    (Hclosed : asep_closed I) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q) :
    ∀ s, asep_state_ok s → I s →
      Auc P (retP RC) (owned_interp (project .child s.cfg)) (s.loc .child) →
      Auc Q (retP RP) (owned_interp (project .parent s.cfg)) (s.loc .parent) →
      Auc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) (owned_interp s.cfg)
        s.global := by
  intro s0 Hok0 HI0 HC0 HP0
  have HRC := asep_pred_ok_entails (Ticl.ret RC)
  have HRP := asep_pred_ok_entails (Ticl.ret RP)
  have HAC := asep_pred_ok_auc P _ HP HRC
  have HAP := asep_pred_ok_auc Q _ HQ HRP
  have HAU := @asep_until_au_proper I P Q RC RP
  have Hmain : ∀ tc wc, Auc P (retP RC) tc wc → ∀ s, asep_state_ok s → I s →
      tc ~ owned_interp (project .child s.cfg) → wc = s.loc .child →
      Auc Q (retP RP) (owned_interp (project .parent s.cfg)) (s.loc .parent) →
      Auc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) (owned_interp s.cfg)
        s.global := by
    intro tc wc HC
    induction HC with
    | @matchA tc wc HCret =>
      have Hparent : ∀ tp wp, Auc Q (retP RP) tp wp → ∀ s, asep_state_ok s → I s →
          tc ~ owned_interp (project .child s.cfg) → wc = s.loc .child →
          tp ~ owned_interp (project .parent s.cfg) → wp = s.loc .parent →
          Auc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) (owned_interp s.cfg)
            s.global := by
        intro tp wp HPa
        induction HPa with
        | @matchA tp wp HPret =>
          intro s Hok HI EC EW EP EWp
          subst EW EWp
          exact .matchA (asep_ret_compose I RC RP _ _ Hclosed (asep_sat_intro I _ _ s
            (asep_at_intro I _ _ s Hok HI (asep_pred_transport _ HRC _ _ _ EC HCret)
              (asep_pred_transport _ HRP _ _ _ EP HPret))))
        | @stepA tp wp HPp HPcan HPk IHp =>
          intro s Hok HI EC EW EP EWp
          subst EW EWp
          have HCz := asep_pred_transport _ HRC _ _ _ EC HCret
          have HPz := asep_pred_transport _ (asep_pred_ok_anc Q _ HQ HAP) _ _ _ EP
            ⟨HPp, HPcan, HPk⟩
          refine .stepA (.inr (.inl (asep_sat_intro I _ _ s (asep_at_intro I _ _ s Hok HI HCz
            HPz.1)))) (asep_progress s Hok (asep_ret_can_step _ _ _ HCz) HPz.2.1) ?_
          intro u v HT
          have Hlive := asep_anc_live s .parent Q _ u v Hok HPz HAP.1 HT
          obtain ⟨s', r, i, Hfront, Eu, rfl, Hmove, Er, Ef, Ewf⟩ :=
            asep_visible_forward_owner s u v Hok HT Hlive
          obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
          cases i with
          | child => exact absurd (Hok'.2.2 .child) (asep_ret_no_live _ _ _ _ _ HCz Hmove)
          | parent =>
            simp only [other] at Ef Ewf
            refine (HAU _ Eu).2 ?_
            obtain ⟨r', Hr', Er'⟩ := ktrans_semiproper (sbisim_symm EP) Hmove
            exact IHp r' _ Hr' s' Hok' HI' (sbisim_trans EC (sbisim_symm Ef)) Ewf.symm
              (sbisim_trans (sbisim_symm Er') Er) rfl
      intro s Hok HI EC EW HPa
      exact Hparent _ _ HPa s Hok HI EC EW (sbisim_refl _) rfl
    | @stepA tc wc HCp HCcan HCk IHc =>
      have Hparent : ∀ tp wp, Auc Q (retP RP) tp wp → ∀ s, asep_state_ok s → I s →
          tc ~ owned_interp (project .child s.cfg) → wc = s.loc .child →
          tp ~ owned_interp (project .parent s.cfg) → wp = s.loc .parent →
          Auc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) (owned_interp s.cfg)
            s.global := by
        intro tp wp HPa
        induction HPa with
        | @matchA tp wp HPret =>
          intro s Hok HI EC EW EP EWp
          subst EW EWp
          have HCz := asep_pred_transport _ (asep_pred_ok_anc P _ HP HAC) _ _ _ EC
            ⟨HCp, HCcan, HCk⟩
          have HPz := asep_pred_transport _ HRP _ _ _ EP HPret
          refine .stepA (.inr (.inr (asep_sat_intro I _ _ s (asep_at_intro I _ _ s Hok HI HCz.1
            HPz)))) (asep_progress s Hok HCz.2.1 (asep_ret_can_step _ _ _ HPz)) ?_
          intro u v HT
          have Hlive := asep_anc_live s .child P _ u v Hok HCz HAC.1 HT
          obtain ⟨s', r, i, Hfront, Eu, rfl, Hmove, Er, Ef, Ewf⟩ :=
            asep_visible_forward_owner s u v Hok HT Hlive
          obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
          cases i with
          | child =>
            simp only [other] at Ef Ewf
            refine (HAU _ Eu).2 ?_
            obtain ⟨r', Hr', Er'⟩ := ktrans_semiproper (sbisim_symm EC) Hmove
            refine IHc r' _ Hr' s' Hok' HI' (sbisim_trans (sbisim_symm Er') Er) rfl
              (.matchA ?_)
            rw [Ewf]; exact asep_pred_transport _ HRP _ _ _ (sbisim_symm Ef) HPz
          | parent => exact absurd (Hok'.2.2 .parent) (asep_ret_no_live _ _ _ _ _ HPz Hmove)
        | @stepA tp wp HPp HPcan HPk IHp =>
          intro s Hok HI EC EW EP EWp
          subst EW EWp
          have HCz := asep_pred_transport _ (asep_pred_ok_anc P _ HP HAC) _ _ _ EC
            ⟨HCp, HCcan, HCk⟩
          have HPz := asep_pred_transport _ (asep_pred_ok_anc Q _ HQ HAP) _ _ _ EP
            ⟨HPp, HPcan, HPk⟩
          refine .stepA (.inl (asep_sat_intro I _ _ s (asep_at_intro I _ _ s Hok HI HCz.1
            HPz.1))) (asep_progress s Hok HCz.2.1 HPz.2.1) ?_
          intro u v HT
          have Hlive := asep_anc_live s .child P _ u v Hok HCz HAC.1 HT
          obtain ⟨s', r, i, Hfront, Eu, rfl, Hmove, Er, Ef, Ewf⟩ :=
            asep_visible_forward_owner s u v Hok HT Hlive
          obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
          refine (HAU _ Eu).2 ?_
          cases i with
          | child =>
            simp only [other] at Ef Ewf
            obtain ⟨r', Hr', Er'⟩ := ktrans_semiproper (sbisim_symm EC) Hmove
            refine IHc r' _ Hr' s' Hok' HI' (sbisim_trans (sbisim_symm Er') Er) rfl ?_
            rw [Ewf]; exact asep_pred_transport _ HAP _ _ _ (sbisim_symm Ef) (.stepA' HPz)
          | parent =>
            simp only [other] at Ef Ewf
            obtain ⟨r', Hr', Er'⟩ := ktrans_semiproper (sbisim_symm EP) Hmove
            exact IHp r' _ Hr' s' Hok' HI' (sbisim_trans EC (sbisim_symm Ef)) Ewf.symm
              (sbisim_trans (sbisim_symm Er') Er) rfl
      intro s Hok HI EC EW HPa
      exact Hparent _ _ HPa s Hok HI EC EW (sbisim_refl _) rfl
  exact Hmain _ _ HC0 s0 Hok0 HI0 (sbisim_refl _) rfl HP0

/-- Universal until over native returns composes. -/
theorem asep_auc_ret_compose (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet)
    (t : AsepTree) (w : AsepWorld) (Hclosed : asep_closed I) (HP : asep_pred_ok P)
    (HQ : asep_pred_ok Q) (H : asep_sat I (Auc P (retP RC)) (Auc Q (retP RP)) t w) :
    Auc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) t w := by
  obtain ⟨s, Et, rfl, Hok, -, HI, HC, HPar⟩ := asep_sat_inv I _ _ t w H
  exact (asep_until_au_proper I P Q RC RP _ Et).2
    (asep_until_auc I P Q RC RP Hclosed HP HQ s Hok HI HC HPar)

/-! ## Existential until by finite ranks -/

theorem asep_euc_rank_ok (P R : AsepPred) (n : Nat) (HP : asep_pred_ok P) (HR : asep_pred_ok R) :
    asep_pred_ok (asep_euc_rank P R n) := by
  induction n with
  | zero => exact HR
  | succ n ih => exact asep_pred_ok_enc P _ HP ih

theorem asep_euc_rank_exists (P R : AsepPred) (t : AsepTree) (w : AsepWorld)
    (H : Euc P R t w) : ∃ n, asep_euc_rank P R n t w := by
  induction H with
  | matchE h => exact ⟨0, h⟩
  | stepE u v hp tr _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, hp, u, v, tr, hn⟩

/-- Focus release uses erased-silent owned actions without consuming a native return transition
or changing either predecessor world. -/
theorem asep_ret_release (s : AsepState) (i : Side) (R : AsepRet) (Hok : asep_state_ok s)
    (HR : (retP R) (owned_interp (project i s.cfg)) (s.loc i)) :
    ∃ s', Star asep_silent s s' ∧ s'.global = s.global ∧ (∀ j, s'.loc j = s.loc j) ∧
      owned_side_ready (other i) s'.cfg := by
  have He := Hok.1
  rcases Hf : s.cfg.pool.focus with _ | j
  · exact ⟨s, .refl, rfl, fun _ => rfl, .inl Hf⟩
  · by_cases Hi : s.cfg.pool.tags[j] = i
    · obtain ⟨d, Hd, H0⟩ := asep_ret_local_frontier _ R _ (owned_active_local _ i He) HR
      obtain ⟨s', Hsil, Eg, El, -, Hnone, -⟩ :=
        asep_local_terminal_lift s i d (.inr ⟨j, Hf, Hi⟩) Hd H0
      exact ⟨s', Hsil, Eg, El, .inl Hnone⟩
    · refine ⟨s, .refl, rfl, fun _ => rfl, .inr ⟨j, Hf, ?_⟩⟩
      generalize s.cfg.pool.tags[j] = x at Hi ⊢
      cases i <;> cases x <;> simp_all [other]

theorem asep_until_eu_lift (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet)
    (s : AsepState) (i : Side) (A R : AsepPred) (Hclosed : asep_closed I)
    (Hok : asep_state_ok s) (HI : I s)
    (Hguard : asep_until_guard I P Q RC RP (owned_interp s.cfg) s.global)
    (Hready : owned_side_ready i s.cfg) (HR : asep_pred_ok R)
    (Henc : enc A R (owned_interp (project i s.cfg)) (s.loc i))
    (Hnext : ∀ s', asep_state_ok s' → I s' →
      R (owned_interp (project i s'.cfg)) (s'.loc i) →
      owned_interp (project (other i) s'.cfg) ~ owned_interp (project (other i) s.cfg) →
      s'.loc (other i) = s.loc (other i) →
      Euc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) (owned_interp s'.cfg)
        s'.global) :
    Euc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) (owned_interp s.cfg)
      s.global := by
  obtain ⟨s', q, Hfront, Hq, Eq, Hpost, Ef, Ew⟩ := asep_enc_ready s i A R Hok Hready HR Henc
  obtain ⟨Hok', HI'⟩ := asep_closed_frontier I s s' Hclosed Hok HI Hfront
  exact .stepE q s'.global Hguard Hq
    ((asep_until_eu_proper I P Q RC RP _ Eq).2 (Hnext s' Hok' HI' Hpost Ef Ew))

theorem asep_until_euc_rank (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet)
    (Hclosed : asep_closed I) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q) :
    ∀ r s v, asep_state_ok v → I v →
      asep_euc_rank P (retP RC) r (owned_interp (project .child v.cfg)) (v.loc .child) →
      asep_euc_rank Q (retP RP) s (owned_interp (project .parent v.cfg)) (v.loc .parent) →
      Euc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) (owned_interp v.cfg)
        v.global := by
  have HRC := asep_pred_ok_entails (Ticl.ret RC)
  have HRP := asep_pred_ok_entails (Ticl.ret RP)
  have HrC := fun n => asep_euc_rank_ok P _ n HP HRC
  have HrP := fun n => asep_euc_rank_ok Q _ n HQ HRP
  intro r
  induction r with
  | zero =>
    intro s
    induction s with
    | zero =>
      intro v Hok HI HC HPz
      exact .matchE (asep_ret_compose I RC RP _ _ Hclosed
        (asep_sat_intro I _ _ v (asep_at_intro I _ _ v Hok HI HC HPz)))
    | succ s IHs =>
      intro v Hok HI HC HPz
      have He := Hok.1
      obtain ⟨mid, Hsil, Eglobal, Elocal, Hready⟩ := asep_ret_release v .child RC Hok HC
      obtain ⟨Hokm, HIm⟩ := asep_closed_silent I v mid Hclosed Hok HI Hsil
      have Hcfg := asep_silent_cfg _ _ Hsil
      have HCk : (retP RC) (owned_interp (project .child mid.cfg)) (mid.loc .child) := by
        rw [Elocal .child]
        exact asep_pred_transport _ HRC _ _ _ (owned_silent_local _ _ .child He Hcfg) HC
      have HPk : asep_euc_rank Q (retP RP) (s + 1) (owned_interp (project .parent mid.cfg))
          (mid.loc .parent) := by
        rw [Elocal .parent]
        exact asep_pred_transport _ (HrP _) _ _ _ (owned_silent_local _ _ .parent He Hcfg) HPz
      rw [← Eglobal]
      refine (asep_until_eu_proper I P Q RC RP _ (owned_interp_silent _ _ He.1 Hcfg)).2 ?_
      refine asep_until_eu_lift I P Q RC RP mid .parent Q _ Hclosed Hokm HIm
        (.inr (.inl (asep_sat_intro I _ _ mid (asep_at_intro I _ _ mid Hokm HIm HCk HPk.1))))
        Hready (HrP s) HPk ?_
      intro v' Hok' HI' Hpost Ef Ew
      simp only [other] at Ef Ew
      refine IHs v' Hok' HI' ?_ Hpost
      rw [Ew]; exact asep_pred_transport _ HRC _ _ _ (sbisim_symm Ef) HCk
  | succ r IHr =>
    intro s
    induction s with
    | zero =>
      intro v Hok HI HC HPz
      have He := Hok.1
      obtain ⟨mid, Hsil, Eglobal, Elocal, Hready⟩ := asep_ret_release v .parent RP Hok HPz
      obtain ⟨Hokm, HIm⟩ := asep_closed_silent I v mid Hclosed Hok HI Hsil
      have Hcfg := asep_silent_cfg _ _ Hsil
      have HCk : asep_euc_rank P (retP RC) (r + 1) (owned_interp (project .child mid.cfg))
          (mid.loc .child) := by
        rw [Elocal .child]
        exact asep_pred_transport _ (HrC _) _ _ _ (owned_silent_local _ _ .child He Hcfg) HC
      have HPk : (retP RP) (owned_interp (project .parent mid.cfg)) (mid.loc .parent) := by
        rw [Elocal .parent]
        exact asep_pred_transport _ HRP _ _ _ (owned_silent_local _ _ .parent He Hcfg) HPz
      rw [← Eglobal]
      refine (asep_until_eu_proper I P Q RC RP _ (owned_interp_silent _ _ He.1 Hcfg)).2 ?_
      refine asep_until_eu_lift I P Q RC RP mid .child P _ Hclosed Hokm HIm
        (.inr (.inr (asep_sat_intro I _ _ mid (asep_at_intro I _ _ mid Hokm HIm HCk.1 HPk))))
        Hready (HrC r) HCk ?_
      intro v' Hok' HI' Hpost Ef Ew
      simp only [other] at Ef Ew
      refine IHr 0 v' Hok' HI' Hpost ?_
      rw [Ew]; exact asep_pred_transport _ HRP _ _ _ (sbisim_symm Ef) HPk
    | succ s IHs =>
      intro v Hok HI HC HPz
      have Hready : ∃ i, owned_side_ready i v.cfg := by
        rcases Hf : v.cfg.pool.focus with _ | j
        · exact ⟨.child, .inl Hf⟩
        · exact ⟨_, .inr ⟨j, Hf, rfl⟩⟩
      obtain ⟨i, Hready⟩ := Hready
      have Hguard : asep_until_guard I P Q RC RP (owned_interp v.cfg) v.global :=
        .inl (asep_sat_intro I _ _ v (asep_at_intro I _ _ v Hok HI HC.1 HPz.1))
      cases i with
      | child =>
        refine asep_until_eu_lift I P Q RC RP v .child P _ Hclosed Hok HI Hguard Hready (HrC r)
          HC ?_
        intro v' Hok' HI' Hpost Ef Ew
        simp only [other] at Ef Ew
        refine IHr (s + 1) v' Hok' HI' Hpost ?_
        rw [Ew]; exact asep_pred_transport _ (HrP _) _ _ _ (sbisim_symm Ef) HPz
      | parent =>
        refine asep_until_eu_lift I P Q RC RP v .parent Q _ Hclosed Hok HI Hguard Hready (HrP s)
          HPz ?_
        intro v' Hok' HI' Hpost Ef Ew
        simp only [other] at Ef Ew
        refine IHs v' Hok' HI' ?_ Hpost
        rw [Ew]; exact asep_pred_transport _ (HrC _) _ _ _ (sbisim_symm Ef) HC

/-- Existential until over native returns composes. -/
theorem asep_euc_ret_compose (I : AsepState → Prop) (P Q : AsepPred) (RC RP : AsepRet)
    (t : AsepTree) (w : AsepWorld) (Hclosed : asep_closed I) (HP : asep_pred_ok P)
    (HQ : asep_pred_ok Q) (H : asep_sat I (Euc P (retP RC)) (Euc Q (retP RP)) t w) :
    Euc (asep_until_guard I P Q RC RP) (retP (asep_ret I RC RP)) t w := by
  obtain ⟨v, Et, rfl, Hok, -, HI, HC, HPar⟩ := asep_sat_inv I _ _ t w H
  obtain ⟨r, Hr⟩ := asep_euc_rank_exists _ _ _ _ HC
  obtain ⟨s, Hs⟩ := asep_euc_rank_exists _ _ _ _ HPar
  exact (asep_until_eu_proper I P Q RC RP _ Et).2
    (asep_until_euc_rank I P Q RC RP Hclosed HP HQ r s v Hok HI Hr Hs)

theorem asep_af_ret_compose (I : AsepState → Prop) (RC RP : AsepRet) (t : AsepTree)
    (w : AsepWorld) (Hclosed : asep_closed I)
    (H : asep_sat I (entails (.cu .A (.now fun _ => True) (.ret RC)))
      (entails (.cu .A (.now fun _ => True) (.ret RP))) t w) :
    entails (.cu .A (.now fun _ => True) (.ret (asep_ret I RC RP))) t w :=
  auc_mono_l (fun _ _ HG => ⟨trivial, asep_until_guard_live _ _ _ _ _ _ _ HG⟩) _ _
    (asep_auc_ret_compose I _ _ RC RP t w Hclosed (asep_pred_ok_entails (.now fun _ => True))
      (asep_pred_ok_entails (.now fun _ => True)) H)

theorem asep_ef_ret_compose (I : AsepState → Prop) (RC RP : AsepRet) (t : AsepTree)
    (w : AsepWorld) (Hclosed : asep_closed I)
    (H : asep_sat I (entails (.cu .E (.now fun _ => True) (.ret RC)))
      (entails (.cu .E (.now fun _ => True) (.ret RP))) t w) :
    entails (.cu .E (.now fun _ => True) (.ret (asep_ret I RC RP))) t w :=
  euc_mono_l (fun _ _ HG => ⟨trivial, asep_until_guard_live _ _ _ _ _ _ _ HG⟩) _ _
    (asep_euc_ret_compose I _ _ RC RP t w Hclosed (asep_pred_ok_entails (.now fun _ => True))
      (asep_pred_ok_entails (.now fun _ => True)) H)

/-! ## Fair existential always -/

/-- One valid owned execution satisfying the separated assertion at every turn, with infinitely
many visible actions of each lineage, gives existential always globally and for each lineage. -/
theorem asep_egc_run (I : AsepState → Prop) (P Q : AsepPred) (s0 : AsepState)
    (e : Execution AsepState OwnedAction PUnit) (HP : asep_pred_ok P) (HQ : asep_pred_ok Q)
    (Hvalid : execution_valid (fun a s (_ : PUnit) s' => asep_step s a s') (Eq s0) e)
    (Hassn : ∀ n, asep_at I P Q (e.states n))
    (Hinf : ∀ i, infinitely fun n =>
      owner_visible i (e.states n).cfg (e.selected n) (e.states (n + 1)).cfg) :
    egc (asep_sat I P Q) (owned_interp s0.cfg) s0.global ∧
      asep_sat I (egc P) (egc Q) (owned_interp s0.cfg) s0.global := by
  obtain ⟨H0, Hrun⟩ := Hvalid
  subst H0
  have Hok : ∀ n, asep_state_ok (e.states n) := fun n => (Hassn n).1
  have Hpair : ∀ n,
      P (owned_interp (project .child (e.states n).cfg)) ((e.states n).loc .child) ∧
      Q (owned_interp (project .parent (e.states n).cfg)) ((e.states n).loc .parent) := by
    intro n
    obtain ⟨-, -, -, h1, h2⟩ := asep_at_inv I P Q _ (Hassn n)
    exact ⟨h1, h2⟩
  have Hlocal : ∀ i, egc (match i with | .child => P | .parent => Q)
      (owned_interp (project i (e.states 0).cfg)) ((e.states 0).loc i) := by
    intro i
    refine egc_of_sequence (fun n => owned_interp (project i (e.states n).cfg))
      (fun n => (e.states n).loc i)
      (fun n => owner_visible i (e.states n).cfg (e.selected n) (e.states (n + 1)).cfg)
      _ (fun _ => Classical.propDecidable _) (Hinf i) ?_ ?_ ?_ ?_ 0
    · intro n; cases i
      · exact (Hpair n).1
      · exact (Hpair n).2
    · cases i
      · exact HP.2
      · exact HQ.2
    · intro n Hn; exact asep_invisible _ _ _ i (Hok n) (Hrun n) Hn
    · rintro n ⟨Ho, Hv⟩
      obtain ⟨u, Hu, Eu⟩ := owned_owner_ktrans _ _ _ i ((e.states n).loc i) (Hok n).1
        (Hrun n).1 Ho Hv ((Hok n).2.2 i)
      refine ⟨u, ?_, Eu⟩
      rw [(Hrun n).2]
      simpa only [asep_advance, Ho, side_eqb_self, ite_true] using Hu
  refine ⟨egc_of_sequence (fun n => owned_interp (e.states n).cfg) (fun n => (e.states n).global)
    (fun n => erase_action_label (e.selected n) (joined_heap (e.states (n + 1)).cfg) ≠ none)
    (asep_sat I P Q) (fun _ => Classical.propDecidable _) ?_
    (fun n => asep_sat_intro I P Q _ (Hassn n))
    (asep_sat_pred_ok I P Q).2 ?_ ?_ 0, ?_⟩
  · intro n
    obtain ⟨m, Hm, -, Hv⟩ := Hinf .child n
    exact ⟨m, Hm, Hv⟩
  · intro n Hn
    have Hnone := Classical.not_not.1 Hn
    refine ⟨owned_interp_silent _ _ (Hok n).1.1 (.single ⟨e.selected n, (Hrun n).1, Hnone⟩), ?_⟩
    rw [(Hrun n).2]
    simp only [asep_advance, action_logs, Hnone, after_logs]
  · intro n Hv
    rcases Hl : erase_action_label (e.selected n) (joined_heap (e.states (n + 1)).cfg)
      with _ | l
    · exact absurd Hl Hv
    obtain ⟨u, Hu, Eu⟩ := owned_interp_visible _ _ _ _ l (Hok n).1.1 .refl (Hrun n).1 Hl
    refine ⟨u, ?_, Eu⟩
    rw [(Hrun n).2]
    exact owned_label_ktrans _ _ l _ u _ Hl Hu (Hok n).2.1
  · exact asep_sat_intro I _ _ _
      (asep_at_intro I _ _ _ (Hok 0) (Hassn 0).2.1 (Hlocal .child) (Hlocal .parent))

-- Not ported: none (every declaration of lines 806-1572 is ported; `asep_ret`,
-- `asep_until_guard` and `asep_euc_rank` live in `Logic/Sep/AsepCore.lean`).

end Tisl.CSL
