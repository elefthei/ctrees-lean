/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Active.OperationalNextRegression

/-!
# Active separation: asynchronous next regression

Both writers of `OperationalNextRegression` start unfocused. Each local next-step target
(`target 1 4` for the child, `target 2 6` for the parent) holds of its own projection, and their
active composition gives the global `AN`/`EN` disjunction. No single global step realises both
targets: the lineage that did not act retains its failed target (← `examples/CSL/Frame/Active.v`,
module `AsyncNextRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.AsyncNextRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm CoCSL
open Examples.CSL.Frame.Shared

def cfg : OwnedCfg :=
  set_pool OperationalNextRegression.cfg
    (mk_pool 2 #v[denote (.write 1 4), denote (.write 2 6)] #v[.child, .parent] none)

def initial : AsepState := { cfg := cfg, global := .pure, loc := fun _ => .pure }

theorem first_action_selects (a : OwnedAction) (c : OwnedCfg) : owned_step cfg a c →
    ∃ j : Fin 2, a = act (#v[.child, .parent] : Vector Side 2)[j] .select ∧
      c = set_pool cfg
        (mk_pool 2 #v[denote (.write 1 4), denote (.write 2 6)] #v[.child, .parent] (some j)) :=
  fun H => H

def yielding : OwnedCfg :=
  init_owned (.write 1 4) (.bind .yield fun _ => .write 2 6) (region 1 3) (region 2 5) [] 0

theorem yielding_admitted :
    admissible (.write 1 4) (.bind .yield fun _ => .write 2 6) (region 1 3) (region 2 5) [] 0 :=
  admissible_regions _ _ _ _ _ _ _ _ (by decide) trivial ⟨trivial, fun _ => trivial⟩
    (by simp [addr_ok, region, hsingle]) (by simp [addr_ok, region, hsingle])

theorem yielding_step : owned_step yielding (act .parent .yield) cfg := by
  show focus_step yielding 1
    #v[denote (.write 1 4), denote (.bind .yield fun _ => .write 2 6)] #v[.child, .parent] 1
    (act .parent .yield) cfg
  refine .inr (.inl ⟨fun _ => denote (.write 2 6), ⟨0, ?_⟩, rfl, rfl⟩)
  simp only [denote, source_raw_bind, source_raw_yield_head]; rfl

theorem initial_ok : asep_state_ok initial :=
  ⟨active_erasable_step _ _ _
    (admissible_active_erasable _ _ _ _ _ _ yielding_admitted) yielding_step,
    .pure, fun _ => .pure⟩

def guard : AsepPred := entails (Ticl.now fun _ => True : TiclL (writerE (CSLObs (Nat × Nat))))

def post (i v : Nat) : PUnit × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop :=
  fun r _ => csl_memory r.2 ≈ region i v ∧ r.2.2 = ([], 0)

def target (i v : Nat) : AsepPred :=
  entails (Ticl.cx .A (.now fun _ => True) (.ret (post i v)))

theorem local_run (i : Side) :
    owned_interp (project i cfg) ~
      interp_schedule_nd sh 1
        #v[denote (match i with | .child => .write 1 4 | .parent => .write 2 6)] none
        (match i with | .child => own 1 3 [] 0 | .parent => own 2 5 [] 0) := by
  unfold owned_interp; rw [owned_joined_state_project]
  have hp : (project i cfg).pool = mk_pool 1 #v[denote (match i with
      | .child => .write 1 4 | .parent => .write 2 6)] #v[i] none := by
    refine tp_equ_eq ⟨?_, rfl⟩
    rw [Forall2_slot_iff]; show tp_slots (project_pool _ _) = _; rw [tp_slots_project]
    cases i <;> simp [proj_slots, proj_indices, fin_all, cfg, set_pool, mk_pool, tp_slots,
      side_eqb, List.finRange_succ] <;>
      first | exact .inl ⟨rfl, rfl, rfl⟩ | exact .inr ⟨rfl, rfl, rfl⟩
  generalize (project i cfg).pool = p at hp ⊢
  subst hp
  cases i <;> exact sbisim_refl _

theorem focused_write (i a v : Nat) :
    anc guard (entails (.ret (post i v)))
      (interp_schedule_nd sh 1 #v[denote (.write i v)] (some 0) (own i a [] 0)) .pure := by
  show entails (Ticl.cx .A (.now fun _ => True) (.ret (post i v))) _ _
  refine (proper_entails_meq _ (interp_nd_source_write_present 0 #v[pure ⟨⟩] 0 i v
    (fun _ => pure ⟨⟩) (hsingle i a) hemp [] 0 (by simp [hsingle_eq]))).2 ?_
  refine ax_log .pure ?_
  rw [proper_entails_meq _ (interp_schedule_nd_ret sh 0 _ 0 _ (by simp)),
    proper_entails_meq _ (interp_schedule_nd_empty sh _ _)]
  exact ret_ret (.obs _ _) (And.intro (upd_region i a v) rfl)

theorem unfocused_write (i a v : Nat) :
    anc guard (target i v)
      (interp_schedule_nd sh 1 #v[denote (.write i v)] none (own i a [] 0)) .pure := by
  refine (an_csl_nd_select 0 (region i a) [] 0 _ .pure (.now fun _ => True)
    (Ticl.cx .A (.now fun _ => True) (.ret (post i v)))).2 ⟨⟨trivial, .pure⟩, fun j => ?_⟩
  obtain rfl := fin1_eq j
  exact focused_write i a v

theorem local_next (i : Side) :
    anc guard (match i with | .child => target 1 4 | .parent => target 2 6)
      (owned_interp (project i cfg)) .pure := by
  cases i <;>
    exact asep_pred_transport _ (asep_pred_ok_anc _ _ (asep_pred_ok_entails _)
      (asep_pred_ok_entails _)) _ _ _ (sbisim_symm (local_run _)) (unfocused_write _ _ _)

theorem pair_next :
    anc guard (target 1 4) (owned_interp (project .child cfg)) .pure ∧
    anc guard (target 2 6) (owned_interp (project .parent cfg)) .pure :=
  ⟨local_next .child, local_next .parent⟩

theorem asynchronous_AN :
    anc (asep_sat (fun _ => True) guard guard)
      (fun t w => asep_sat (fun _ => True) (target 1 4) guard t w ∨
        asep_sat (fun _ => True) guard (target 2 6) t w)
      (owned_interp cfg) .pure :=
  asep_anc_compose _ _ _ _ _ _ _ asep_closed_true (asep_pred_ok_entails _)
    (asep_pred_ok_entails _) (asep_pred_ok_entails _) (asep_pred_ok_entails _)
    (asep_sat_intro _ _ _ initial
      (asep_at_intro _ _ _ initial initial_ok trivial pair_next.1 pair_next.2))

private theorem anc_enc {P Q : AsepPred} {t : AsepTree} {w : AsepWorld} (H : anc P Q t w) :
    enc P Q t w :=
  let ⟨HG, ⟨u, v, HT⟩, HN⟩ := H
  ⟨HG, u, v, HT, HN u v HT⟩

theorem asynchronous_EN :
    enc (asep_sat (fun _ => True) guard guard)
      (fun t w => asep_sat (fun _ => True) (target 1 4) guard t w ∨
        asep_sat (fun _ => True) guard (target 2 6) t w)
      (owned_interp cfg) .pure :=
  asep_enc_compose _ _ _ _ _ _ _ asep_closed_true (asep_pred_ok_entails _)
    (asep_pred_ok_entails _) (asep_pred_ok_entails _) (asep_pred_ok_entails _)
    (asep_sat_intro _ _ _ initial
      (asep_at_intro _ _ _ initial initial_ok trivial (anc_enc (local_next .child))
        (anc_enc (local_next .parent))))

theorem local_target_false (i : Side) :
    ¬ (match i with | .child => target 1 4 | .parent => target 2 6)
      (owned_interp (project i cfg)) .pure := by
  intro H
  have K : ∀ n a v, entails (Ticl.cx .A (.now fun _ => True) (.ret (post n v)))
      (interp_schedule_nd sh 1 #v[denote (.write n v)] none (own n a [] 0)) .pure → False := by
    intro n a v H
    obtain ⟨x, -, -, -, HN⟩ :=
      ((an_csl_nd_select 0 (region n a) [] 0 _ .pure (.now fun _ => True) _).1 H).2 0
    obtain ⟨-, ⟨u, w, HT⟩, HP⟩ := focused_write n a v
    have Hw := ticl_not_done _ (HP u w HT)
    cases HN u w HT <;> cases Hw
  cases i
  · exact K 1 3 4 ((proper_entails_meq _ (local_run .child)).1 H)
  · exact K 2 5 6 ((proper_entails_meq _ (local_run .parent)).1 H)

theorem retained_foreign_excludes_targets (t : AsepTree) (w : AsepWorld) (s : AsepState) :
    ktrans (owned_interp cfg) .pure t w → NotDone w →
    asep_frontier initial s → t ~ owned_interp s.cfg → w = s.global →
    (owned_interp (project .child s.cfg) ~ owned_interp (project .child cfg) ∧
        s.loc .child = .pure ∨
      owned_interp (project .parent s.cfg) ~ owned_interp (project .parent cfg) ∧
        s.loc .parent = .pure) →
    ¬ asep (local_obligation .child (target 1 4) s)
        (local_obligation .parent (target 2 6) s) (joined_heap s.cfg) := by
  intro _ _ Hfront _ _ Hforeign HI
  have Hok := (asep_closed_frontier (fun _ => True) initial s asep_closed_true initial_ok
    trivial Hfront).1
  obtain ⟨TC, TP⟩ := (asep_local_pinned s _ _ Hok.1.1.1).1 HI
  rcases Hforeign with ⟨E, W⟩ | ⟨E, W⟩
  · rw [W] at TC
    exact local_target_false .child (asep_pred_transport _ (asep_pred_ok_entails _) _ _ _ E TC)
  · rw [W] at TP
    exact local_target_false .parent (asep_pred_transport _ (asep_pred_ok_entails _) _ _ _ E TP)

theorem global_next_retains_failed_target (t : AsepTree) (w : AsepWorld) :
    ktrans (owned_interp cfg) .pure t w → NotDone w →
    ∃ s, asep_frontier initial s ∧ t ~ owned_interp s.cfg ∧ w = s.global ∧
      ¬ asep (local_obligation .child (target 1 4) s)
          (local_obligation .parent (target 2 6) s) (joined_heap s.cfg) := by
  intro HT Hw
  obtain ⟨s, u, i, Hfront, Et, Ew, HC⟩ := asep_visible_forward_owner initial t w initial_ok HT Hw
  refine ⟨s, Hfront, Et, Ew,
    retained_foreign_excludes_targets t w s HT Hw Hfront Et Ew ?_⟩
  cases i
  · exact .inr HC.2.2
  · exact .inl HC.2.2

theorem one_action_excludes_both (a : OwnedAction) (d : OwnedCfg) : owned_step cfg a d →
    ¬ asep (local_obligation .child (target 1 4) (asep_advance initial a d))
        (local_obligation .parent (target 2 6) (asep_advance initial a d)) (joined_heap d) := by
  intro HS HI
  obtain ⟨HC, HP⟩ := (asep_local_pinned (asep_advance initial a d) _ _
    (active_erasable_step cfg a d initial_ok.1 HS).1.1).1 HI
  rcases a with ⟨o, k⟩
  cases o
  · have E : owned_interp (project .parent d) ~ owned_interp (project .parent cfg) :=
      owned_interp_equ _ _ (owned_step_foreign .parent cfg _ d HS nofun)
    exact local_target_false .parent
      (asep_pred_transport _ (asep_pred_ok_entails _) _ _ .pure E HP)
  · have E : owned_interp (project .child d) ~ owned_interp (project .child cfg) :=
      owned_interp_equ _ _ (owned_step_foreign .child cfg _ d HS nofun)
    exact local_target_false .child
      (asep_pred_transport _ (asep_pred_ok_entails _) _ _ .pure E HC)

theorem no_initial_silent (d : OwnedCfg) : ¬ silent_next cfg d := by
  rintro ⟨a, HS, HL⟩
  obtain ⟨j, rfl, -⟩ := first_action_selects a d HS
  cases HL

theorem initial_silent_refl (d : OwnedCfg) : Star silent_next cfg d → d = cfg := fun H =>
  match H.cases_head with
  | .inl h => h.symm
  | .inr ⟨y, h, _⟩ => (no_initial_silent y h).elim

theorem global_next_exactly_one_action (t : AsepTree) (w : AsepWorld) :
    ktrans (owned_interp cfg) .pure t w → NotDone w →
    ∃ a d, owned_step cfg a d ∧ asep_step initial a (asep_advance initial a d) ∧
      t ~ owned_interp d ∧ w = (asep_advance initial a d).global ∧
      ¬ asep (local_obligation .child (target 1 4) (asep_advance initial a d))
          (local_obligation .parent (target 2 6) (asep_advance initial a d)) (joined_heap d) := by
  intro HT Hw
  obtain ⟨d, a, d', l, Hsil, HS, -, ET, EW⟩ :=
    owned_ktrans_forward cfg .pure t w initial_ok.1.1 .pure HT Hw
  obtain rfl := initial_silent_refl d Hsil
  exact ⟨a, d', HS, ⟨HS, rfl⟩, ET, EW, one_action_excludes_both a d' HS⟩

-- Not ported: Rocq `Local Abbreviation Pred` (the type `AsepPred` of `Logic/Sep/AsepCore`).

end Examples.CSL.Frame.Active.AsyncNextRegression
