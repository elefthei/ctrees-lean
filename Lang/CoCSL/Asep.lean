/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.AsepSplit

/-!
# Owned proofs transported to the original TICL judgments

Canonical execution transports TICL formulas from `owned_interp` to the raw runner; finite owned
eventualities (`hAF`/`hEF` of `hDone`), owned invariants (`hAG`) and fair owned runs yield the
corresponding TICL judgments, and the fork bridges specialise them to `run_nd (bind (fork child) k)`
(← `Lang/CoCSL/Asep.v`, lines 1104-1574).
-/

@[expose] public section
namespace CoCSL
open CTree Coinduction Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Notation
open ITree (Effect)

/-- Raw runner observations. -/
local notation "OW" => World (writerE (CSLObs (Nat × Nat)))
/-- Raw runner trees. -/
local notation "OT" => ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)

/-- Every tree conditionally simulates itself up to `owned_result_rel`. -/
private theorem csim_owned_refl (t : OT) : csim event_eq owned_result_rel t t := by
  refine gfp_prop (b := csimF event_eq owned_result_rel) (P := fun R => ∀ t, R t t)
    (tower (fun T hT t => Rel.inf_apply.2 fun R hR => hT R hR t) ?_) t
  intro R _ IH t
  have hL : ∀ l u, trans l t u → simL event_eq owned_result_rel l l := by
    intro l u ht
    cases l with
    | tau => exact .tau
    | obs e v => exact .obs e e v v rfl HEq.rfl
    | val x =>
      cases trans_val_invT ht
      exact .val x x ⟨rfl, rfl, peq_refl _⟩
  exact ⟨fun l t' ht => ⟨l, t', ht, hL _ _ ht, IH t'⟩,
    fun _ l u' hu => ⟨l, u', hu, hL _ _ hu, IH u'⟩⟩

/-- Canonical execution transports arbitrary formulas between related worlds; native return
predicates retain the full `owned_result_rel` contract. -/
theorem owned_ticl_transport (c : OwnedCfg) {b : Bool}
    (p : TiclAt (writerE (CSLObs (Nat × Nat))) (PUnit × SSig) b) (w w' : OW)
    (_ : erasable c) (HW : simW event_eq owned_result_rel w w')
    (Hp : entails p (owned_interp c) w) :
    entails (framer (PUnit × SSig) b event_eq owned_result_rel p)
      (interp_schedule_nd sh c.pool.size c.pool.threads c.pool.focus (joined_state c)) w' := by
  refine ticl_csim b event_eq owned_result_rel p ?_ _ _ w w' (csim_owned_refl _) HW Hp
  cases b
  · trivial
  · exact ⟨event_eq_right_unique, owned_result_rel_right_unique⟩

theorem silent_owned_reach (c d : OwnedCfg) (H : Star silent_next c d) : Star owned_next c d :=
  Star.mono (fun _ _ ⟨a, Hs, _⟩ => ⟨a, Hs⟩) H

theorem owned_reach_before (c d e : OwnedCfg) (H : Star owned_next c d) :
    Relation.TransGen (fun y x => owned_next x y) e d →
      Relation.TransGen (fun y x => owned_next x y) e c := by
  induction H with
  | refl => exact id
  | tail _ hbd ih => exact fun H => ih (.tail H hbd)

theorem erased_visible_world (a : OwnedAction) (post : ManagedHeap)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (t u : OT) (w : OW)
    (HL : erase_action_label a post = some l) (Hw : NotDone w) (HT : trans l t u) :
    ∃ w', ktrans t w u w' ∧ NotDone w' := by
  rcases erase_label_shape a post l HL with ⟨rfl, -⟩ | ⟨o, rfl⟩
  · exact ⟨w, .tau Hw HT, Hw⟩
  · exact ⟨_, .obs o ⟨⟩ Hw HT, .obs _ _⟩

/-- Inversion keeps exact configurations; only the computed residual uses ordinary
bisimulation. In particular this does not use `owned_equ`. -/
theorem erased_terminal_world (t u : OT) (r : PUnit × SSig) (w : OW) (Hw : NotDone w)
    (HT : trans (.val r) t u) :
    ∃ w', ktrans t w u w' ∧ DoneWith (fun r' _ => r' = r) w' := by
  cases Hw with
  | pure => exact ⟨_, .done r HT, .done r rfl⟩
  | obs e v => exact ⟨_, .finish e v r HT, .finish e v r rfl⟩

theorem haf_done_next (Q : hprop) (c d : OwnedCfg) (H : hAF owned_next (hDone Q) c)
    (Hs : owned_next c d) : hAF owned_next (hDone Q) d :=
  hAU_ind owned_next hTrue (hDone Q) (fun c => owned_next c d → hAF owned_next (hDone Q) d)
    (fun c ⟨Ht, _⟩ ⟨a, Hs⟩ => absurd Hs (owned_step_empty c a d Ht))
    (fun _ _ _ H _ Hs => H d Hs) c H Hs

theorem haf_done_reach (Q : hprop) (c d : OwnedCfg) (Hr : Star owned_next c d)
    (H : hAF owned_next (hDone Q) c) : hAF owned_next (hDone Q) d := by
  induction Hr with
  | refl => exact H
  | tail _ hbd ih => exact haf_done_next Q _ _ ih hbd

theorem haf_done_terminal (Q : hprop) (c : OwnedCfg) (H : hAF owned_next (hDone Q) c)
    (Ht : terminal c) : Q c :=
  hAU_ind owned_next hTrue (hDone Q) (fun c => terminal c → Q c)
    (fun _ ⟨_, HQ⟩ _ => HQ)
    (fun c _ ⟨d, a, Hs⟩ _ _ Ht => absurd Hs (owned_step_empty c a d Ht)) c H Ht

theorem haf_done_acc (Q : hprop) (c : OwnedCfg) (H : hAF owned_next (hDone Q) c) :
    Acc (fun d c => owned_next c d) c :=
  hAU_ind owned_next hTrue (hDone Q) (fun c => Acc (fun d c => owned_next c d) c)
    (fun c ⟨Ht, _⟩ => .intro c fun d ⟨a, Hs⟩ => absurd Hs (owned_step_empty c a d Ht))
    (fun c _ _ _ IH => .intro c IH) c H

/-- A finite owned proof supplies either a terminal silent frontier, where native return closes
immediately, or a genuine visible successor. -/
theorem haf_done_frontier (Q : hprop) (c : OwnedCfg) (H : hAF owned_next (hDone Q) c) :
    ∃ d, Star silent_next c d ∧
      (terminal d ∨ ∃ a d' l, owned_step d a d' ∧ erase_action_label a (joined_heap d') = some l) :=
  hAU_ind owned_next hTrue (hDone Q)
    (fun c => ∃ d, Star silent_next c d ∧
      (terminal d ∨ ∃ a d' l, owned_step d a d' ∧ erase_action_label a (joined_heap d') = some l))
    (fun c ⟨Ht, _⟩ => ⟨c, .refl, .inl Ht⟩)
    (fun c _ ⟨d, a, Hs⟩ _ IH => by
      rcases HL : erase_action_label a (joined_heap d) with _ | l
      · obtain ⟨e, Hp, Hf⟩ := IH d ⟨a, Hs⟩
        exact ⟨e, Star.head ⟨a, Hs, HL⟩ Hp, Hf⟩
      · exact ⟨c, .refl, .inr ⟨a, d, l, Hs, HL⟩⟩) c H

theorem haf_done_can_raw (Q : hprop) (c : OwnedCfg) (w : OW) (He : erasable c) (Hw : NotDone w)
    (HA : hAF owned_next (hDone Q) c) : can_step (owned_interp c) w := by
  obtain ⟨d, Hp, Ht | ⟨a, d', l, Hs, HL⟩⟩ := haf_done_frontier Q c HA
  · obtain ⟨T, HT, -⟩ := owned_interp_terminal_trans c d He Hp Ht
    obtain ⟨w', HW, -⟩ := erased_terminal_world _ _ _ _ Hw HT
    exact ⟨T, w', HW⟩
  · obtain ⟨T, HT, -⟩ := owned_interp_visible c d a d' l He Hp Hs HL
    obtain ⟨w', HW, -⟩ := erased_visible_world a _ l _ _ _ HL Hw HT
    exact ⟨T, w', HW⟩

/-- A silent prefix to a terminal configuration makes the canonical runner a return. -/
private theorem owned_interp_ret (c d : OwnedCfg) (He : erasable c) (Hp : Star silent_next c d)
    (Ht : terminal d) : owned_interp c ~ (pure (PUnit.unit, joined_state d) : OT) :=
  sbisim_trans (owned_interp_silent c d He Hp)
    (owned_interp_terminal d (erasable_reach c d He (silent_owned_reach c d Hp)) Ht)

theorem owned_haf_ret_ticl (Q : PUnit × SSig → Prop) (c : OwnedCfg) (w : OW) (He : erasable c)
    (Hw : NotDone w) (_ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HA : hAF owned_next (hDone fun d => Q (PUnit.unit, joined_state d)) c) :
    entails (AF (.ret fun r _ => Q r) : TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig))
      (owned_interp c) w := by
  have Hacc := (haf_done_acc _ c HA).transGen
  have H : ∀ d, Acc (Relation.TransGen fun y x => owned_next x y) d → ∀ (t : OT) z,
      t ~ owned_interp d → erasable d → NotDone z →
      hAF owned_next (hDone fun d => Q (PUnit.unit, joined_state d)) d →
      Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
        (entails (.ret fun r _ => Q r : TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig)))
        t z := by
    intro d hacc
    induction hacc with
    | intro d _ IH =>
    intro t z HB He0 Hz HA0
    obtain ⟨f, Hp, Ht | ⟨a, f', l, Hs, HL⟩⟩ := haf_done_frontier _ d HA0
    · refine .matchA ((proper_entails_meq (meq := sbisim Eq) _
        (sbisim_trans HB (owned_interp_ret d f He0 Hp Ht))).2 ?_)
      exact ret_ret (R := fun r _ => Q r) Hz
        (haf_done_terminal _ f (haf_done_reach _ d f (silent_owned_reach d f Hp) HA0) Ht)
    · obtain ⟨V, HV, -⟩ := owned_interp_visible d f a f' l He0 Hp Hs HL
      obtain ⟨zv, HWV, Hzv⟩ := erased_visible_world a _ l _ _ _ HL Hz HV
      refine .stepA ⟨trivial, Hz⟩
        ((proper_can_step (meq := sbisim Eq) HB).2 ⟨V, zv, HWV⟩) fun T z' HT => ?_
      obtain ⟨U, HU, HTU⟩ := ktrans_semiproper HB HT
      by_cases Hz' : NotDone z'
      · obtain ⟨g, b, g', l', Hpg, Hsg, -, HUf, -⟩ := owned_ktrans_forward d z U z' He0 Hz HU Hz'
        have Hr := silent_owned_reach d g Hpg
        exact IH g' (owned_reach_before d g g' Hr (.single ⟨b, Hsg⟩)) T z'
          (sbisim_trans HTU HUf) (erasable_step _ b _ (erasable_reach d g He0 Hr) Hsg) Hz'
          (haf_done_next _ g g' (haf_done_reach _ d g Hr HA0) ⟨b, Hsg⟩)
      · exfalso
        obtain ⟨g, Hpg, Htg, -, -⟩ := owned_ktrans_terminal d z U z' He0 HU Hz'
        have HR : entails (.ret fun _ _ => True :
            TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig)) (owned_interp d) z :=
          (proper_entails_meq (meq := sbisim Eq) _ (owned_interp_ret d g He0 Hpg Htg)).2
            (ret_ret (R := fun _ _ => True) Hz trivial)
        obtain ⟨r, -, -, -, Hret⟩ := HR
        cases Hret V zv HWV <;> cases Hzv
  exact H c Hacc _ w (sbisim_refl _) He Hw HA

theorem owned_haf_done_ticl (Q : PUnit × SSig → Prop) (c : OwnedCfg) (w : OW) (He : erasable c)
    (Hw : NotDone w) (HQ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HA : hAF owned_next (hDone fun d => Q (PUnit.unit, joined_state d)) c) :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (fun r _ => Q r) wd) (owned_interp c) w :=
  af_ret_done _ (owned_haf_ret_ticl Q c w He Hw HQ HA)

theorem owned_hef_ret_ticl (Q : PUnit × SSig → Prop) (c : OwnedCfg) (w : OW) (He : erasable c)
    (Hw : NotDone w) (_ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HE : hEF owned_next (hDone fun d => Q (PUnit.unit, joined_state d)) c) :
    entails (EF (.ret fun r _ => Q r) : TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig))
      (owned_interp c) w := by
  refine hEU_ind owned_next hTrue (hDone fun d => Q (PUnit.unit, joined_state d))
    (fun d => ∀ start, erasable start → Star silent_next start d → ∀ (w : OW), NotDone w →
      entails (EF (.ret fun r _ => Q r) : TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig))
        (owned_interp start) w) ?_ ?_ c HE c He .refl w Hw
  · intro d ⟨Ht, HQ⟩ start He0 Hp z Hz
    exact .matchE ((proper_entails_meq (meq := sbisim Eq) _
      (owned_interp_ret start d He0 Hp Ht)).2 (ret_ret (R := fun r _ => Q r) Hz HQ))
  · intro d d' _ ⟨a, Hs⟩ _ IH start He0 Hp z Hz
    rcases HL : erase_action_label a (joined_heap d') with _ | l
    · exact IH start He0 (Hp.tail ⟨a, Hs, HL⟩) z Hz
    · obtain ⟨T, HT, HB⟩ := owned_interp_visible start d a d' l He0 Hp Hs HL
      obtain ⟨z', HW, Hz'⟩ := erased_visible_world a _ l _ _ _ HL Hz HT
      refine .stepE T z' ⟨trivial, Hz⟩ HW ((proper_entails_meq (meq := sbisim Eq)
        (EF (.ret fun r _ => Q r) : TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig))
        HB).2 ?_)
      exact IH d' (erasable_step _ a _ (erasable_reach start d He0 (silent_owned_reach _ _ Hp)) Hs)
        .refl z' Hz'

theorem owned_hef_done_ticl (Q : PUnit × SSig → Prop) (c : OwnedCfg) (w : OW) (He : erasable c)
    (Hw : NotDone w) (HQ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HE : hEF owned_next (hDone fun d => Q (PUnit.unit, joined_state d)) c) :
    Euc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (fun r _ => Q r) wd) (owned_interp c) w :=
  ef_ret_done _ (owned_hef_ret_ticl Q c w He Hw HQ HE)

theorem hag_owned_reach (I : hprop) (c d : OwnedCfg) (Hr : Star owned_next c d)
    (HG : hAG owned_next I c) : hAG owned_next I d := by
  induction Hr with
  | refl => exact HG
  | tail _ hbd ih => exact ((hAG_unfold _ _ _).1 ih).2.2 _ hbd

theorem hag_visible_frontier (I : hprop) (rank : OwnedCfg → Nat)
    (Hrank : ∀ d a d', I d → owned_step d a d' →
      erase_action_label a (joined_heap d') = none → rank d' < rank d) :
    ∀ c, hAG owned_next I c →
      ∃ d a d' l, Star silent_next c d ∧ owned_step d a d' ∧
        erase_action_label a (joined_heap d') = some l := by
  have H : ∀ bound c, rank c < bound → hAG owned_next I c →
      ∃ d a d' l, Star silent_next c d ∧ owned_step d a d' ∧
        erase_action_label a (joined_heap d') = some l := by
    intro bound
    induction bound with
    | zero => intro c Hb; omega
    | succ bound IH =>
      intro c Hb HG
      obtain ⟨HI, ⟨d, a, Hs⟩, HN⟩ := (hAG_unfold _ _ _).1 HG
      rcases HL : erase_action_label a (joined_heap d) with _ | l
      · obtain ⟨f, b, f', l, Hp, Hb', Hbl⟩ :=
          IH d (by have := Hrank c a d HI Hs HL; omega) (HN d ⟨a, Hs⟩)
        exact ⟨f, b, f', l, Star.head ⟨a, Hs, HL⟩ Hp, Hb', Hbl⟩
      · exact ⟨c, a, d, l, .refl, Hs, HL⟩
  exact fun c HG => H (rank c + 1) c (Nat.lt_succ_self _) HG

theorem owned_hag_ticl (I : hprop) (rank : OwnedCfg → Nat) (c : OwnedCfg) (w : OW)
    (He : erasable c) (Hw : NotDone w) (_ : hproper I)
    (Hrank : ∀ d a d', I d → owned_step d a d' →
      erase_action_label a (joined_heap d') = none → rank d' < rank d)
    (HG : hAG owned_next I c) :
    entails (AG (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) (owned_interp c) w := by
  let Z : OT → OW → Prop := fun t z =>
    NotDone z ∧ ∃ d, erasable d ∧ hAG owned_next I d ∧ t ~ owned_interp d
  have HZ : ∀ t z, Z t z → agcF (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) Z t z := by
    rintro t z ⟨Hz, d, He0, HG0, HB⟩
    refine ⟨⟨trivial, Hz⟩, ?_, fun T z' HT => ?_⟩
    · obtain ⟨f, a, f', l, Hp, Hs, HL⟩ := hag_visible_frontier I rank Hrank d HG0
      obtain ⟨T, HT, -⟩ := owned_interp_visible d f a f' l He0 Hp Hs HL
      obtain ⟨z', HW, -⟩ := erased_visible_world a _ l _ _ _ HL Hz HT
      obtain ⟨U, HU, -⟩ := ktrans_semiproper (sbisim_symm HB) HW
      exact ⟨U, z', HU⟩
    · obtain ⟨U, HU, HTU⟩ := ktrans_semiproper HB HT
      by_cases Hz' : NotDone z'
      · obtain ⟨f, a, f', l, Hp, Hs, -, HUf, -⟩ := owned_ktrans_forward d z U z' He0 Hz HU Hz'
        have Hr := silent_owned_reach d f Hp
        exact ⟨Hz', f', erasable_step _ a _ (erasable_reach d f He0 Hr) Hs,
          ((hAG_unfold _ _ _).1 (hag_owned_reach I d f Hr HG0)).2.2 f' ⟨a, Hs⟩,
          sbisim_trans HTU HUf⟩
      · obtain ⟨f, Hp, Ht, -, -⟩ := owned_ktrans_terminal d z U z' He0 HU Hz'
        obtain ⟨-, ⟨f', a, Hs⟩, -⟩ :=
          (hAG_unfold _ _ _).1 (hag_owned_reach I d f (silent_owned_reach d f Hp) HG0)
        exact absurd Hs (owned_step_empty f a f' Ht)
  exact le_gfp (b := agcF _) (x := Z) HZ _ _ ⟨Hw, c, He, HG, sbisim_refl _⟩

theorem owned_run_interval (e : Execution OwnedCfg OwnedAction Unit) (Hrun : owned_run e)
    (n len : Nat) : Star owned_next (e.states n) (e.states (n + len)) := by
  induction len with
  | zero => exact .refl
  | succ len ih => exact ih.tail ⟨e.selected (n + len), Hrun (n + len)⟩

theorem owned_run_silent_interval (e : Execution OwnedCfg OwnedAction Unit) (Hrun : owned_run e)
    (n len : Nat)
    (Hall : ∀ j, n ≤ j ∧ j < n + len →
      erase_action_label (e.selected j) (joined_heap (e.states (j + 1))) = none) :
    Star silent_next (e.states n) (e.states (n + len)) := by
  induction len with
  | zero => exact .refl
  | succ len ih =>
    exact (ih fun j hj => Hall j ⟨hj.1, by omega⟩).tail
      ⟨e.selected (n + len), Hrun (n + len), Hall _ ⟨by omega, by omega⟩⟩

theorem owned_run_visible_frontier (e : Execution OwnedCfg OwnedAction Unit)
    (Hrun : owned_run e)
    (Hinf : infinitely fun n =>
      erase_action_label (e.selected n) (joined_heap (e.states (n + 1))) ≠ none) (n : Nat) :
    ∃ m l, n ≤ m ∧ erase_action_label (e.selected m) (joined_heap (e.states (m + 1))) = some l ∧
      Star silent_next (e.states n) (e.states m) := by
  obtain ⟨bound, Hbound, Hvis⟩ := Hinf n
  rcases finite_first (fun j =>
      erase_action_label (e.selected j) (joined_heap (e.states (j + 1))) ≠ none)
      (fun _ => Classical.propDecidable _) n (bound + 1 - n) with
    Hnone | ⟨m, Hm, Hvisible, Hfirst⟩
  · exact absurd Hvis (Hnone bound ⟨Hbound, by omega⟩)
  · rcases HL : erase_action_label (e.selected m) (joined_heap (e.states (m + 1))) with _ | l
    · exact absurd HL Hvisible
    · have Hp := owned_run_silent_interval e Hrun n (m - n) fun j hj =>
        Classical.byContradiction (Hfirst j ⟨hj.1, by omega⟩)
      rw [show n + (m - n) = m by omega] at Hp
      exact ⟨m, l, Hm.1, HL, Hp⟩

theorem owned_heg_ticl (c : OwnedCfg) (w : OW) (e : Execution OwnedCfg OwnedAction Unit)
    (He : erasable c) (Hw : NotDone w) (H0 : e.states 0 = c) (Hrun : owned_run e)
    (Hinf : infinitely fun n =>
      erase_action_label (e.selected n) (joined_heap (e.states (n + 1))) ≠ none) :
    entails (EG (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) (owned_interp c) w := by
  subst H0
  have Herasable : ∀ n, erasable (e.states n) := fun n =>
    erasable_reach _ _ He (Nat.zero_add n ▸ owned_run_interval e Hrun 0 n)
  let Z : OT → OW → Prop := fun t z => NotDone z ∧ ∃ n, t ~ owned_interp (e.states n)
  have HZ : ∀ t z, Z t z → egcF (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat))))) Z t z := by
    rintro t z ⟨Hz, n, HB⟩
    refine ⟨⟨trivial, Hz⟩, ?_⟩
    obtain ⟨m, l, -, HL, Hp⟩ := owned_run_visible_frontier e Hrun Hinf n
    obtain ⟨T, HT, HTm⟩ := owned_interp_visible _ _ _ _ l (Herasable n) Hp (Hrun m) HL
    obtain ⟨z', HW, Hz'⟩ := erased_visible_world _ _ l _ _ _ HL Hz HT
    obtain ⟨U, HU, HTU⟩ := ktrans_semiproper (sbisim_symm HB) HW
    exact ⟨U, z', HU, Hz', m + 1, sbisim_trans (sbisim_symm HTU) HTm⟩
  exact le_gfp (b := egcF _) (x := Z) HZ _ _ ⟨Hw, 0, sbisim_refl _⟩

/-! ## Fork bridges -/

section ForkTiclBridges
variable (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
  (base : Nat)

theorem fork_ticl {b : Bool} (p : TiclAt (writerE (CSLObs (Nat × Nat))) (PUnit × SSig) b)
    (w : OW) :
    entails p (owned_interp (init_owned child (k ()) h h' ctx base)) w ↔
      entails p (run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base))) w :=
  proper_entails_meq (meq := sbisim Eq) p (owned_fork_runner child k h h' ctx base)

theorem fork_haf_ret_ticl (Q : PUnit × SSig → Prop)
    (Hadm : admissible child (k ()) h h' ctx base)
    (HQ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HA : hAF owned_next (hDone fun d => Q (PUnit.unit, joined_state d))
      (init_owned child (k ()) h h' ctx base)) :
    entails (AF (.ret fun r _ => Q r) : TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig))
      (run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base))) .pure :=
  (fork_ticl child k h h' ctx base (b := true) _ .pure).1
    (owned_haf_ret_ticl Q _ .pure (admissible_erasable _ _ _ _ _ _ Hadm) .pure HQ HA)

theorem fork_haf_done_ticl (Q : PUnit × SSig → Prop)
    (Hadm : admissible child (k ()) h h' ctx base)
    (HQ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HA : hAF owned_next (hDone fun d => Q (PUnit.unit, joined_state d))
      (init_owned child (k ()) h h' ctx base)) :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (fun r _ => Q r) wd)
      (run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base))) .pure :=
  af_ret_done _ (fork_haf_ret_ticl child k h h' ctx base Q Hadm HQ HA)

theorem fork_hef_ret_ticl (Q : PUnit × SSig → Prop)
    (Hadm : admissible child (k ()) h h' ctx base)
    (HQ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HE : hEF owned_next (hDone fun d => Q (PUnit.unit, joined_state d))
      (init_owned child (k ()) h h' ctx base)) :
    entails (EF (.ret fun r _ => Q r) : TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig))
      (run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base))) .pure :=
  (fork_ticl child k h h' ctx base (b := true) _ .pure).1
    (owned_hef_ret_ticl Q _ .pure (admissible_erasable _ _ _ _ _ _ Hadm) .pure HQ HE)

theorem fork_hef_done_ticl (Q : PUnit × SSig → Prop)
    (Hadm : admissible child (k ()) h h' ctx base)
    (HQ : ∀ r r', owned_result_rel r r' → (Q r ↔ Q r'))
    (HE : hEF owned_next (hDone fun d => Q (PUnit.unit, joined_state d))
      (init_owned child (k ()) h h' ctx base)) :
    Euc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (fun r _ => Q r) wd)
      (run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base))) .pure :=
  ef_ret_done _ (fork_hef_ret_ticl child k h h' ctx base Q Hadm HQ HE)

theorem fork_hag_ticl (I : hprop) (rank : OwnedCfg → Nat)
    (Hadm : admissible child (k ()) h h' ctx base) (HI : hproper I)
    (Hrank : ∀ d a d', I d → owned_step d a d' →
      erase_action_label a (joined_heap d') = none → rank d' < rank d)
    (HG : hAG owned_next I (init_owned child (k ()) h h' ctx base)) :
    entails (AG (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base))) .pure :=
  (fork_ticl child k h h' ctx base (b := false) _ .pure).1
    (owned_hag_ticl I rank _ .pure (admissible_erasable _ _ _ _ _ _ Hadm) .pure HI Hrank HG)

theorem fork_heg_ticl (e : Execution OwnedCfg OwnedAction Unit)
    (Hadm : admissible child (k ()) h h' ctx base)
    (H0 : e.states 0 = init_owned child (k ()) h h' ctx base) (Hrun : owned_run e)
    (Hinf : infinitely fun n =>
      erase_action_label (e.selected n) (joined_heap (e.states (n + 1))) ≠ none) :
    entails (EG (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (run_nd (.bind (.fork child) k) (h ⊎ h', (ctx, base))) .pure :=
  (fork_ticl child k h h' ctx base (b := false) _ .pure).1
    (owned_heg_ticl _ .pure e (admissible_erasable _ _ _ _ _ _ Hadm) .pure H0 Hrun Hinf)

end ForkTiclBridges

end CoCSL
