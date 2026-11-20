/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.AsepModal
public import Logic.Sep.AsepCore
public import Lang.CoCSL.Owned

/-!
# Splitting TICL properties of forked CoCSL programs

Global properties of an admitted fork, stated over the anchored split `state_sat` with ordinary
heap `asep`, imply properties of each projected component. Finite modalities split
unconditionally; `AN` needs selection-stable targets, `AG` release certificates, and `EG` one
execution fair to both lineages (← `Lang/CoCSL/Asep.v`, lines 390-1103).
-/

@[expose] public section
namespace CoCSL
open Tisl Tisl.CSL Tisl.Pcm Tisl.Heap Tisl.Ctx

/-! ## Finite modalities on the global clock -/

/-- A global `AU` read on lineage `i` is a local `AU` of its projection. -/
theorem global_hau_project (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q →
    hAU owned_next (at_side i P) (at_side i Q) c → hAU owned_next P Q (project i c) := by
  intro _ _
  refine hAU_ind owned_next _ _ (fun c => hAU owned_next P Q (project i c))
    (fun c Hq => hAU_now _ _ _ _ Hq) (fun c Hp Hcan _ IH => ?_) c
  rcases scheduler_shape i c Hcan with Hst | ⟨Hloc, Hlift⟩
  · obtain ⟨c1, a, Hs⟩ := Hcan
    rw [← owned_equ_eq (owned_step_foreign i c a c1 Hs (Hst a c1 Hs))]
    exact IH c1 ⟨a, Hs⟩
  · refine hAU_step _ _ _ _ Hp Hloc fun d' ⟨a', Hs'⟩ => ?_
    obtain ⟨a, c1, Hs, -, -, He⟩ := Hlift a' d' Hs'
    rw [← owned_equ_eq He]
    exact IH c1 ⟨a, Hs⟩

/-- A global `EU` read on lineage `i` is a local `EU` of its projection. -/
theorem global_heu_project (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q →
    hEU owned_next (at_side i P) (at_side i Q) c → hEU owned_next P Q (project i c) := by
  intro _ _
  refine hEU_ind owned_next _ _ (fun c => hEU owned_next P Q (project i c))
    (fun c Hq => hEU_now _ _ _ _ Hq) (fun c c1 Hp ⟨a, Hs⟩ _ IH => ?_) c
  by_cases Ho : a.owner = i
  · obtain ⟨d', Hs', He⟩ := owned_step_own i c a c1 Hs Ho
    rw [owned_equ_eq He] at IH
    exact hEU_step _ _ _ _ d' Hp ⟨_, Hs'⟩ IH
  · rwa [← owned_equ_eq (owned_step_foreign i c a c1 Hs Ho)]

theorem global_hau_split (P P' Q Q' : hprop) (c : OwnedCfg) :
    coupled c → hproper P → hproper P' → hproper Q → hproper Q' →
    hAU owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c)) c →
    hAU owned_next P Q (project .child c) ∧ hAU owned_next P' Q' (project .parent c) := by
  intro _ HP HP' HQ HQ' H
  exact ⟨global_hau_project _ _ _ _ HP HQ (hAU_mono _ _ _ _ _ _
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1)
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1) H),
    global_hau_project _ _ _ _ HP' HQ' (hAU_mono _ _ _ _ _ _
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2)
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2) H)⟩

theorem global_heu_split (P P' Q Q' : hprop) (c : OwnedCfg) :
    coupled c → hproper P → hproper P' → hproper Q → hproper Q' →
    hEU owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c)) c →
    hEU owned_next P Q (project .child c) ∧ hEU owned_next P' Q' (project .parent c) := by
  intro _ HP HP' HQ HQ' H
  exact ⟨global_heu_project _ _ _ _ HP HQ (hEU_mono _ _ _ _ _ _
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1)
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1) H),
    global_heu_project _ _ _ _ HP' HQ' (hEU_mono _ _ _ _ _ _
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2)
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2) H)⟩

theorem global_haf_split (Q Q' : hprop) (c : OwnedCfg) :
    coupled c → hproper Q → hproper Q' →
    hAF owned_next
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c)) c →
    hAF owned_next Q (project .child c) ∧ hAF owned_next Q' (project .parent c) := by
  intro _ HQ HQ' H
  exact ⟨global_hau_project _ _ _ _ hTrue_proper HQ (hAU_mono _ _ _ _ _ _
      (fun _ _ => trivial) (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1) H),
    global_hau_project _ _ _ _ hTrue_proper HQ' (hAU_mono _ _ _ _ _ _
      (fun _ _ => trivial) (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2) H)⟩

theorem global_hef_split (Q Q' : hprop) (c : OwnedCfg) :
    coupled c → hproper Q → hproper Q' →
    hEF owned_next
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c)) c →
    hEF owned_next Q (project .child c) ∧ hEF owned_next Q' (project .parent c) := by
  intro _ HQ HQ' H
  exact ⟨global_heu_project _ _ _ _ hTrue_proper HQ (hEU_mono _ _ _ _ _ _
      (fun _ _ => trivial) (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1) H),
    global_heu_project _ _ _ _ hTrue_proper HQ' (hEU_mono _ _ _ _ _ _
      (fun _ _ => trivial) (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2) H)⟩

/-! ## The own-action clock -/

theorem weak_can_local (i : Side) (c : OwnedCfg) :
    hcan_step (weak_next i) c → hcan_step owned_next (project i c) := by
  rintro ⟨c1, Hw⟩
  obtain ⟨d', Hs, -⟩ := weak_next_sound i c c1 Hw
  exact ⟨d', Hs⟩

theorem weak_han_to_local (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q →
    hAN (weak_next i) (at_side i P) (at_side i Q) c → hAN owned_next P Q (project i c) := by
  intro _ _ H
  obtain ⟨Hp, Hs, Hall⟩ := (hAN_iff _ _ _ _).1 H
  refine (hAN_iff _ _ _ _).2 ⟨Hp, weak_can_local i c Hs, fun d' Hd => ?_⟩
  obtain ⟨c1, Hw, He⟩ := weak_next_complete i c Hs d' Hd
  rw [← owned_equ_eq He]
  exact Hall c1 Hw

theorem weak_hen_to_local (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q →
    hEN (weak_next i) (at_side i P) (at_side i Q) c → hEN owned_next P Q (project i c) := by
  intro _ _ H
  obtain ⟨Hp, c1, Hw, Hq⟩ := (hEN_iff _ _ _ _).1 H
  obtain ⟨d', Hs, He⟩ := weak_next_sound i c c1 Hw
  exact (hEN_iff _ _ _ _).2 ⟨Hp, d', Hs, owned_equ_eq He ▸ Hq⟩

theorem weak_hau_to_local (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q →
    hAU (weak_next i) (at_side i P) (at_side i Q) c → hAU owned_next P Q (project i c) := by
  intro _ _
  refine hAU_ind (weak_next i) _ _ (fun c => hAU owned_next P Q (project i c))
    (fun c Hq => hAU_now _ _ _ _ Hq) (fun c Hp Hcan _ IH => ?_) c
  refine hAU_step _ _ _ _ Hp (weak_can_local i c Hcan) fun d' Hd => ?_
  obtain ⟨c1, Hw, He⟩ := weak_next_complete i c Hcan d' Hd
  rw [← owned_equ_eq He]
  exact IH c1 Hw

theorem weak_heu_to_local (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q →
    hEU (weak_next i) (at_side i P) (at_side i Q) c → hEU owned_next P Q (project i c) := by
  intro _ _
  refine hEU_ind (weak_next i) _ _ (fun c => hEU owned_next P Q (project i c))
    (fun c Hq => hEU_now _ _ _ _ Hq) (fun c c1 Hp Hw _ IH => ?_) c
  obtain ⟨d', Hs, He⟩ := weak_next_sound i c c1 Hw
  rw [owned_equ_eq He] at IH
  exact hEU_step _ _ _ _ d' Hp Hs IH

theorem weak_hag_to_local (i : Side) (P : hprop) (c : OwnedCfg) :
    hproper P → hAG (weak_next i) (at_side i P) c → hAG owned_next P (project i c) := by
  intro _ HG
  refine hAG_coind owned_next P
    (fun d => ∃ c, hAG (weak_next i) (at_side i P) c ∧ project i c = d) ?_ _ ⟨c, HG, rfl⟩
  rintro _ ⟨c, HG, rfl⟩
  obtain ⟨Hp, Hs, Hn⟩ := (hAG_unfold _ _ _).1 HG
  refine ⟨Hp, weak_can_local i c Hs, fun d' Hd => ?_⟩
  obtain ⟨c1, Hw, He⟩ := weak_next_complete i c Hs d' Hd
  exact ⟨c1, Hn c1 Hw, owned_equ_eq He⟩

theorem weak_heg_to_local (i : Side) (P : hprop) (c : OwnedCfg) :
    hproper P → hEG (weak_next i) (at_side i P) c → hEG owned_next P (project i c) := by
  intro _ HG
  refine hEG_coind owned_next P
    (fun d => ∃ c, hEG (weak_next i) (at_side i P) c ∧ project i c = d) ?_ _ ⟨c, HG, rfl⟩
  rintro _ ⟨c, HG, rfl⟩
  obtain ⟨Hp, c1, Hw, HG1⟩ := (hEG_unfold _ _ _).1 HG
  obtain ⟨d', Hs, He⟩ := weak_next_sound i c c1 Hw
  exact ⟨Hp, d', Hs, c1, HG1, owned_equ_eq He⟩

theorem weak_hax_to_local (i : Side) (Q : hprop) (c : OwnedCfg) :
    hproper Q → hAX (weak_next i) (at_side i Q) c → hAX owned_next Q (project i c) :=
  fun HQ H => weak_han_to_local i hTrue Q c hTrue_proper HQ
    (hAN_mono _ _ _ _ _ _ (fun _ _ => trivial) (fun _ h => h) H)

theorem weak_hex_to_local (i : Side) (Q : hprop) (c : OwnedCfg) :
    hproper Q → hEX (weak_next i) (at_side i Q) c → hEX owned_next Q (project i c) :=
  fun HQ H => weak_hen_to_local i hTrue Q c hTrue_proper HQ
    (hEN_mono _ _ _ _ _ _ (fun _ _ => trivial) (fun _ h => h) H)

theorem weak_haf_to_local (i : Side) (Q : hprop) (c : OwnedCfg) :
    hproper Q → hAF (weak_next i) (at_side i Q) c → hAF owned_next Q (project i c) :=
  fun HQ H => weak_hau_to_local i hTrue Q c hTrue_proper HQ
    (hAU_mono _ _ _ _ _ _ (fun _ _ => trivial) (fun _ h => h) H)

theorem weak_hef_to_local (i : Side) (Q : hprop) (c : OwnedCfg) :
    hproper Q → hEF (weak_next i) (at_side i Q) c → hEF owned_next Q (project i c) :=
  fun HQ H => weak_heu_to_local i hTrue Q c hTrue_proper HQ
    (hEU_mono _ _ _ _ _ _ (fun _ _ => trivial) (fun _ h => h) H)

theorem weak_hdone_to_local (i : Side) (P : hprop) (c : OwnedCfg) :
    at_side i (hDone P) c → hDone P (project i c) :=
  fun H => H

theorem weak_hret_to_local (i : Side) (P : hprop) (c : OwnedCfg) :
    hproper P → hRet_at i (weak_next i) P c → hRet owned_next P (project i c) := by
  rintro _ ⟨out, Hout, Hall⟩
  obtain ⟨dout, Hdout, Eout⟩ := weak_next_sound i c out Hout
  refine ⟨dout, Hdout, fun d' Hs => ?_⟩
  obtain ⟨c1, Hw, He⟩ := weak_next_complete i c ⟨out, Hout⟩ d' Hs
  obtain rfl := owned_equ_eq He
  obtain rfl := owned_equ_eq Eout
  exact Hall c1 Hw

/-! ## Next: the explicit two-program frame theorem -/

theorem global_han_owned (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q → OwnEnabled i c →
    hAN owned_next (at_side i P) (at_side i Q) c → hAN owned_next P Q (project i c) := by
  rintro _ _ ⟨Hloc, Hlift⟩ H
  obtain ⟨Hp, -, Hall⟩ := (hAN_iff _ _ _ _).1 H
  refine (hAN_iff _ _ _ _).2 ⟨Hp, Hloc, fun d' ⟨a', Hs'⟩ => ?_⟩
  obtain ⟨a, c1, Hs, -, -, He⟩ := Hlift a' d' Hs'
  rw [← owned_equ_eq He]
  exact Hall c1 ⟨a, Hs⟩

theorem global_hen_owned (i : Side) (P Q : hprop) (c : OwnedCfg) (a : OwnedAction)
    (c' : OwnedCfg) :
    hproper Q → P (project i c) → owned_step c a c' → a.owner = i → Q (project i c') →
    hEN owned_next P Q (project i c) := by
  intro _ Hp Hs Ho Hq
  obtain ⟨d', Hs', He⟩ := owned_step_own i c a c' Hs Ho
  exact (hEN_iff _ _ _ _).2 ⟨Hp, d', ⟨_, Hs'⟩, owned_equ_eq He ▸ Hq⟩

/-- One side of the `AN` split: a stuttering lineage only awaits selection. -/
theorem global_han_side (i : Side) (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q → 0 < (project i c).pool.size → SelectionStable Q →
    hAN owned_next (at_side i P) (at_side i Q) c → hAN owned_next P Q (project i c) := by
  intro HP HQ Hsz HS H
  obtain ⟨Hp, Hcan, Hall⟩ := (hAN_iff _ _ _ _).1 H
  rcases scheduler_shape i c Hcan with Hst | Hen
  · obtain ⟨-, Hloc, Hsel⟩ := stutter_select i c Hcan Hst Hsz
    have Hq : Q (project i c) := by
      obtain ⟨c1, a, Hs⟩ := Hcan
      rw [← owned_equ_eq (owned_step_foreign i c a c1 Hs (Hst a c1 Hs))]
      exact Hall c1 ⟨a, Hs⟩
    exact (hAN_iff _ _ _ _).2
      ⟨Hp, Hloc, fun d' ⟨a', Hs'⟩ => (HS _ _ _ Hs' (Hsel a' d' Hs')).1 Hq⟩
  · exact global_han_owned i P Q c HP HQ Hen H

theorem global_han_split (P P' Q Q' : hprop) (c : OwnedCfg) :
    coupled c → hproper P → hproper P' → hproper Q → hproper Q' →
    0 < (project .child c).pool.size → 0 < (project .parent c).pool.size →
    SelectionStable Q → SelectionStable Q' →
    hAN owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c)) c →
    hAN owned_next P Q (project .child c) ∧ hAN owned_next P' Q' (project .parent c) := by
  intro _ HP HP' HQ HQ' HC HPa HS HS' H
  exact ⟨global_han_side _ _ _ _ HP HQ HC HS (hAN_mono _ _ _ _ _ _
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1)
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1) H),
    global_han_side _ _ _ _ HP' HQ' HPa HS' (hAN_mono _ _ _ _ _ _
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2)
      (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2) H)⟩

theorem global_hax_split (Q Q' : hprop) (c : OwnedCfg) :
    coupled c → hproper Q → hproper Q' →
    0 < (project .child c).pool.size → 0 < (project .parent c).pool.size →
    SelectionStable Q → SelectionStable Q' →
    hAX owned_next
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c)) c →
    hAX owned_next Q (project .child c) ∧ hAX owned_next Q' (project .parent c) := by
  intro _ HQ HQ' HC HPa HS HS' H
  exact ⟨global_han_side _ _ _ _ hTrue_proper HQ HC HS (hAN_mono _ _ _ _ _ _
      (fun _ _ => trivial) (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1) H),
    global_han_side _ _ _ _ hTrue_proper HQ' HPa HS' (hAN_mono _ _ _ _ _ _
      (fun _ _ => trivial) (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2) H)⟩

/-! ## Always: release certificates -/

def step_closed (I : hprop) : Prop := ∀ d a d', I d → owned_step d a d' → I d'

/-- From every progressing invariant state, lineage `i` is enabled after finitely many
rank-decreasing foreign actions. -/
def finite_release (i : Side) (I : hprop) (rank : OwnedCfg → Nat) : Prop :=
  ∀ d, I d → hcan_step owned_next d →
    OwnEnabled i d ∨ ∃ d', foreign_next i d d' ∧ I d' ∧ rank d' < rank d

/-- Finitely many rank-decreasing foreign steps reach an enabled state with the same
projection. -/
theorem release_descent (i : Side) (I : hprop) (rank : OwnedCfg → Nat) (P : hprop) :
    step_closed I → finite_release i I rank →
    ∀ n c, rank c < n → I c → hAG owned_next P c →
    ∃ c1, I c1 ∧ hAG owned_next P c1 ∧ OwnEnabled i c1 ∧
      owned_equ (project i c1) (project i c) := by
  intro _ Hrel n
  induction n with
  | zero => intro _ Hr; exact absurd Hr (Nat.not_lt_zero _)
  | succ n IH =>
    intro c Hr HI HG
    obtain ⟨-, Hcan, Hsucc⟩ := (hAG_unfold _ _ _).1 HG
    rcases Hrel c HI Hcan with Hen | ⟨c', ⟨a, Hst, Hown⟩, HI', Hlt⟩
    · exact ⟨c, HI, HG, Hen, owned_equ_Equivalence.refl _⟩
    · obtain ⟨c1, HI1, HG1, Hen1, Heq1⟩ :=
        IH c' (by omega) HI' (Hsucc c' ⟨a, Hst⟩)
      exact ⟨c1, HI1, HG1, Hen1,
        owned_equ_Equivalence.trans Heq1 (owned_step_foreign i c a c' Hst Hown)⟩

theorem global_hag_one (i : Side) (I : hprop) (rank : OwnedCfg → Nat) (P : hprop)
    (c : OwnedCfg) :
    hproper P → I c → step_closed I → finite_release i I rank →
    hAG owned_next (at_side i P) c → hAG owned_next P (project i c) := by
  intro _ HI Hcl Hrel HG
  refine hAG_coind owned_next P
    (fun d => ∃ c, I c ∧ hAG owned_next (at_side i P) c ∧ project i c = d) ?_ _ ⟨c, HI, HG, rfl⟩
  rintro _ ⟨c0, HI0, HG0, rfl⟩
  obtain ⟨c1, HI1, HG1, ⟨Hcan1, Hlift⟩, Heq1⟩ :=
    release_descent i I rank (at_side i P) Hcl Hrel (rank c0 + 1) c0 (Nat.lt_succ_self _) HI0 HG0
  have HP0 : P (project i c0) := ((hAG_unfold _ _ _).1 HG0).1
  rw [← owned_equ_eq Heq1] at HP0 ⊢
  refine ⟨HP0, Hcan1, fun d' ⟨a', Hst1⟩ => ?_⟩
  obtain ⟨a, c', Hst, -, -, Heqc'⟩ := Hlift a' d' Hst1
  exact ⟨c', Hcl _ _ _ HI1 Hst, ((hAG_unfold _ _ _).1 HG1).2.2 c' ⟨a, Hst⟩, owned_equ_eq Heqc'⟩

theorem global_hag_split (I : hprop) (rankC rankP : OwnedCfg → Nat) (P P' : hprop)
    (c : OwnedCfg) :
    coupled c → hproper P → hproper P' → I c → step_closed I →
    finite_release .child I rankC → finite_release .parent I rankP →
    hAG owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c)) c →
    hAG owned_next P (project .child c) ∧ hAG owned_next P' (project .parent c) := by
  intro _ HP HP' HI Hcl HrC HrP HG
  exact ⟨global_hag_one .child I rankC P c HP HI Hcl HrC
      (hAG_mono _ _ _ _ (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.1) HG),
    global_hag_one .parent I rankP P' c HP' HI Hcl HrP
      (hAG_mono _ _ _ _ (fun d Hd => ((state_split_iff _ _ d).1 Hd).2.2) HG)⟩

/-! ## Exists-always: one fair witness execution -/

def owned_run (e : Execution OwnedCfg OwnedAction Unit) : Prop :=
  ∀ n, owned_step (e.states n) (e.selected n) (e.states (n + 1))

theorem global_heg_fair_one (i : Side) (P : hprop) (c : OwnedCfg)
    (e : Execution OwnedCfg OwnedAction Unit) :
    hproper P → e.states 0 = c → owned_run e →
    (∀ n, P (project i (e.states n))) →
    infinitely (fun n => (e.selected n).owner = i) →
    hEG owned_next P (project i c) := by
  intro _ H0 Hrun HPn Hinf
  subst c
  -- The own action at `n` is one local step of the projection.
  have Hown : ∀ n, (e.selected n).owner = i →
      ∃ d', owned_next (project i (e.states n)) d' ∧ ∃ m, project i (e.states m) = d' := by
    intro n Hi
    obtain ⟨d1, Hst1, Heq1⟩ := owned_step_own i _ _ _ (Hrun n) Hi
    exact ⟨d1, ⟨_, Hst1⟩, n + 1, owned_equ_eq Heq1⟩
  -- Bounded search for the first own action; foreign ones keep the projection.
  have Hfirst : ∀ k n, (e.selected (n + k)).owner = i →
      ∃ d', owned_next (project i (e.states n)) d' ∧ ∃ m, project i (e.states m) = d' := by
    intro k
    induction k with
    | zero => exact fun n Hk => Hown n Hk
    | succ k IH =>
      intro n Hk
      by_cases Hi : (e.selected n).owner = i
      · exact Hown n Hi
      · rw [← owned_equ_eq (owned_step_foreign i _ _ _ (Hrun n) Hi)]
        exact IH (n + 1) (by rwa [show n + 1 + k = n + (k + 1) by omega])
  refine hEG_coind owned_next P (fun d => ∃ n, project i (e.states n) = d) ?_ _ ⟨0, rfl⟩
  rintro _ ⟨n, rfl⟩
  obtain ⟨m0, Hle, Hm0⟩ := Hinf n
  refine ⟨HPn n, Hfirst (m0 - n) n ?_⟩
  rwa [Nat.add_sub_cancel' Hle]

theorem global_heg_fair_split (P P' : hprop) (c : OwnedCfg)
    (e : Execution OwnedCfg OwnedAction Unit) :
    coupled c → hproper P → hproper P' → e.states 0 = c → owned_run e →
    (∀ n, state_sat (fun c => asep (state_obligation .child P c)
      (state_obligation .parent P' c)) (e.states n)) →
    infinitely (fun n => (e.selected n).owner = .child) →
    infinitely (fun n => (e.selected n).owner = .parent) →
    hEG owned_next P (project .child c) ∧ hEG owned_next P' (project .parent c) := by
  intro _ HP HP' H0 Hrun Hsep HinfC HinfP
  exact ⟨global_heg_fair_one .child P c e HP H0 Hrun
      (fun n => ((state_split_iff _ _ _).1 (Hsep n)).2.1) HinfC,
    global_heg_fair_one .parent P' c e HP' H0 Hrun
      (fun n => ((state_split_iff _ _ _).1 (Hsep n)).2.2) HinfP⟩

/-! ## Terminal and returning suffixes -/

theorem global_hdone_split (P Q : hprop) (c : OwnedCfg) :
    hDone (state_sat fun c => asep (state_obligation .child P c)
      (state_obligation .parent Q c)) c →
    hDone P (project .child c) ∧ hDone Q (project .parent c) := by
  rintro ⟨Ht, Hsplit⟩
  obtain ⟨-, Hp, Hq⟩ := (state_split_iff _ _ _).1 Hsplit
  exact ⟨⟨project_size_terminal _ _ Ht, Hp⟩, ⟨project_size_terminal _ _ Ht, Hq⟩⟩

/-- The returning lineage of a last global step. -/
theorem hret_side (i : Side) (P : hprop) (out c : OwnedCfg) (a : OwnedAction) (c1 : OwnedCfg) :
    hproper P → owned_step c a c1 → a.owner = i →
    (∀ c', owned_next c c' → terminal c' ∧ same_view c' out ∧ at_side i P c') →
    hRet owned_next P (project i c) := by
  intro _ Hs Ho Hall
  rcases scheduler_shape i c ⟨c1, a, Hs⟩ with Hst | ⟨-, Hlift⟩
  · exact absurd Ho (Hst a c1 Hs)
  obtain ⟨dout, Hdout, Eout⟩ := owned_step_own i c a c1 Hs Ho
  obtain ⟨Ht1, Hr1, -⟩ := Hall c1 ⟨a, Hs⟩
  refine ⟨dout, ⟨_, Hdout⟩, fun d' ⟨a', Hs'⟩ => ?_⟩
  obtain ⟨b, c', Hb, -, -, He⟩ := Hlift a' d' Hs'
  obtain ⟨Ht, Hr, Hp⟩ := Hall c' ⟨b, Hb⟩
  obtain rfl := owned_equ_eq He
  obtain rfl := owned_equ_eq Eout
  have sv := same_view_equivalence
  exact ⟨project_size_terminal i c' Ht,
    sv.trans (same_view_project i c' out Ht Hr) (sv.symm (same_view_project i c1 out Ht1 Hr1)),
    Hp⟩

/-- The other lineage was already done. -/
theorem hdone_side (j : Side) (P : hprop) (c : OwnedCfg) (a : OwnedAction) (c1 : OwnedCfg) :
    hproper P → owned_step c a c1 → a.owner ≠ j → terminal c1 → at_side j P c1 →
    hDone P (project j c) := by
  intro _ Hs Ho Ht Hp
  rw [← owned_equ_eq (owned_step_foreign j c a c1 Hs Ho)]
  exact ⟨project_size_terminal j c1 Ht, Hp⟩

/-- One global step cannot return both lineages. -/
theorem global_hret_split (P Q : hprop) (c : OwnedCfg) :
    hproper P → hproper Q →
    hRet owned_next (state_sat fun c => asep (state_obligation .child P c)
      (state_obligation .parent Q c)) c →
    (hRet owned_next P (project .child c) ∧ hDone Q (project .parent c)) ∨
    (hDone P (project .child c) ∧ hRet owned_next Q (project .parent c)) := by
  rintro HP HQ ⟨c1, ⟨a, Hs⟩, Hall⟩
  obtain ⟨Ht, -, Hsplit⟩ := Hall c1 ⟨a, Hs⟩
  obtain ⟨-, Hp, Hq⟩ := (state_split_iff _ _ _).1 Hsplit
  have Hside : ∀ c', owned_next c c' →
      terminal c' ∧ same_view c' c1 ∧ P (project .child c') ∧ Q (project .parent c') :=
    fun c' Hn =>
      let ⟨Ht', Hr', Hsplit'⟩ := Hall c' Hn
      let ⟨_, Hp', Hq'⟩ := (state_split_iff _ _ _).1 Hsplit'
      ⟨Ht', Hr', Hp', Hq'⟩
  cases Ho : a.owner with
  | child =>
    exact .inl ⟨hret_side .child P c1 c a c1 HP Hs Ho fun c' Hn =>
        let ⟨h1, h2, h3, _⟩ := Hside c' Hn; ⟨h1, h2, h3⟩,
      hdone_side .parent Q c a c1 HQ Hs (by rw [Ho]; decide) Ht Hq⟩
  | parent =>
    exact .inr ⟨hdone_side .child P c a c1 HP Hs (by rw [Ho]; decide) Ht Hp,
      hret_side .parent Q c1 c a c1 HQ Hs Ho fun c' Hn =>
        let ⟨h1, h2, _, h4⟩ := Hside c' Hn; ⟨h1, h2, h4⟩⟩

/-! ## Source corollaries at the outer fork -/

theorem hproper_transport (P : hprop) (c d : OwnedCfg) : hproper P → owned_equ c d → P c → P d :=
  fun HP Heq => (HP c d Heq).1

theorem init_local_same_view (i : Side) (p : CProg Unit) (h : ManagedHeap) (ctx : Ctx)
    (base : Nat) : same_view (init_local i p h ctx base false) (init_local i p h ctx base true) :=
  ⟨fun _ => peq_refl _, rfl, rfl, fun _ => rfl, fun _ => rfl, Iff.rfl⟩

theorem init_local_next (i : Side) (p : CProg Unit) (h : ManagedHeap) (ctx : Ctx) (base : Nat) :
    owned_next (init_local i p h ctx base false) (init_local i p h ctx base true) :=
  ⟨act i .select, (init_local_select _ _ _ _ _ _ _).2 ⟨rfl, rfl⟩⟩

/-- The projected child still owes its selection; for predicates that only read the heap view,
that step can be stripped. -/
theorem hAU_select_strip (i : Side) (p : CProg Unit) (h : ManagedHeap) (ctx : Ctx) (base : Nat)
    (P Q : hprop) :
    view_pred P → view_pred Q →
    hAU owned_next P Q (init_local i p h ctx base false) →
    hAU owned_next P Q (init_local i p h ctx base true) := by
  intro _ HQ HU
  rcases hAU_ind owned_next P Q
      (fun c => Q c ∨ ∀ c', owned_next c c' → hAU owned_next P Q c')
      (fun _ Hc => .inl Hc) (fun _ _ _ Hs _ => .inr Hs) _ HU with Hq | Hs
  · exact hAU_now _ _ _ _ (HQ _ _ (init_local_same_view i p h ctx base) Hq)
  · exact Hs _ (init_local_next i p h ctx base)

theorem hEU_select_strip (i : Side) (p : CProg Unit) (h : ManagedHeap) (ctx : Ctx) (base : Nat)
    (P Q : hprop) :
    view_pred P → view_pred Q →
    hEU owned_next P Q (init_local i p h ctx base false) →
    hEU owned_next P Q (init_local i p h ctx base true) := by
  intro _ HQ HE0
  rcases hEU_ind owned_next P Q
      (fun c => Q c ∨ ∃ c', owned_next c c' ∧ hEU owned_next P Q c')
      (fun _ Hc => .inl Hc) (fun _ c' _ Hc' HE _ => .inr ⟨c', Hc', HE⟩) _ HE0 with
    Hq | ⟨c', ⟨a, Hst⟩, HE⟩
  · exact hEU_now _ _ _ _ (HQ _ _ (init_local_same_view i p h ctx base) Hq)
  · obtain ⟨-, rfl⟩ := (init_local_select _ _ _ _ _ _ _).1 Hst
    exact HE

/-- `AG` already holds at every successor: no stability assumption. -/
theorem hAG_select_strip (i : Side) (p : CProg Unit) (h : ManagedHeap) (ctx : Ctx) (base : Nat)
    (P : hprop) :
    hAG owned_next P (init_local i p h ctx base false) →
    hAG owned_next P (init_local i p h ctx base true) :=
  fun HG => ((hAG_unfold _ _ _).1 HG).2.2 _ (init_local_next i p h ctx base)

theorem fork_hau_split (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (P P' Q Q' : hprop) :
    admissible child (k ()) h h' ctx base →
    hproper P → hproper P' → hproper Q → hproper Q' →
    hAU owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c))
      (init_owned child (k ()) h h' ctx base) →
    hAU owned_next P Q (init_local .child child h ctx base false) ∧
    hAU owned_next P' Q' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HP HP' HQ HQ' HU
  obtain ⟨HC, HPa⟩ := global_hau_split P P' Q Q' _ (coupled_init _ _ _ _ _ _ Hadm) HP HP' HQ HQ' HU
  rw [owned_equ_eq (project_init_child ..)] at HC
  rw [owned_equ_eq (project_init_parent ..)] at HPa
  exact ⟨HC, HPa⟩

theorem fork_heu_split (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (P P' Q Q' : hprop) :
    admissible child (k ()) h h' ctx base →
    hproper P → hproper P' → hproper Q → hproper Q' →
    hEU owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c))
      (init_owned child (k ()) h h' ctx base) →
    hEU owned_next P Q (init_local .child child h ctx base false) ∧
    hEU owned_next P' Q' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HP HP' HQ HQ' HE
  obtain ⟨HC, HPa⟩ := global_heu_split P P' Q Q' _ (coupled_init _ _ _ _ _ _ Hadm) HP HP' HQ HQ' HE
  rw [owned_equ_eq (project_init_child ..)] at HC
  rw [owned_equ_eq (project_init_parent ..)] at HPa
  exact ⟨HC, HPa⟩

/-- Heap-view assertions at the conventional focused singletons. -/
theorem fork_hau_split_view (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (P P' Q Q' : hprop) :
    admissible child (k ()) h h' ctx base →
    view_pred P → view_pred P' → view_pred Q → view_pred Q' →
    hAU owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c))
      (init_owned child (k ()) h h' ctx base) →
    hAU owned_next P Q (init_local .child child h ctx base true) ∧
    hAU owned_next P' Q' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HP HP' HQ HQ' HU
  obtain ⟨HC, HPa⟩ := fork_hau_split child k h h' ctx base P P' Q Q' Hadm
    (view_pred_proper _ HP) (view_pred_proper _ HP') (view_pred_proper _ HQ)
    (view_pred_proper _ HQ') HU
  exact ⟨hAU_select_strip _ _ _ _ _ P Q HP HQ HC, HPa⟩

theorem fork_heu_split_view (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (P P' Q Q' : hprop) :
    admissible child (k ()) h h' ctx base →
    view_pred P → view_pred P' → view_pred Q → view_pred Q' →
    hEU owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c))
      (init_owned child (k ()) h h' ctx base) →
    hEU owned_next P Q (init_local .child child h ctx base true) ∧
    hEU owned_next P' Q' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HP HP' HQ HQ' HE
  obtain ⟨HC, HPa⟩ := fork_heu_split child k h h' ctx base P P' Q Q' Hadm
    (view_pred_proper _ HP) (view_pred_proper _ HP') (view_pred_proper _ HQ)
    (view_pred_proper _ HQ') HE
  exact ⟨hEU_select_strip _ _ _ _ _ P Q HP HQ HC, HPa⟩

/-- Both projections of the initial fork are singleton pools. -/
private theorem init_project_size (child parent : CProg Unit) (h h' : ManagedHeap) (ctx : Ctx)
    (base : Nat) (i : Side) :
    0 < (project i (init_owned child parent h h' ctx base)).pool.size := by
  cases i
  · rw [owned_equ_eq (project_init_child ..)]; exact Nat.one_pos
  · rw [owned_equ_eq (project_init_parent ..)]; exact Nat.one_pos

theorem fork_han_split (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (P P' Q Q' : hprop) :
    admissible child (k ()) h h' ctx base →
    hproper P → hproper P' → hproper Q → hproper Q' →
    SelectionStable Q → SelectionStable Q' →
    hAN owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c))
      (init_owned child (k ()) h h' ctx base) →
    hAN owned_next P Q (init_local .child child h ctx base false) ∧
    hAN owned_next P' Q' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HP HP' HQ HQ' HsQ HsQ' HN
  obtain ⟨HC, HPa⟩ := global_han_split P P' Q Q' _ (coupled_init _ _ _ _ _ _ Hadm)
    HP HP' HQ HQ' (init_project_size ..) (init_project_size ..) HsQ HsQ' HN
  rw [owned_equ_eq (project_init_child ..)] at HC
  rw [owned_equ_eq (project_init_parent ..)] at HPa
  exact ⟨HC, HPa⟩

theorem fork_hax_split (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (Q Q' : hprop) :
    admissible child (k ()) h h' ctx base →
    hproper Q → hproper Q' → SelectionStable Q → SelectionStable Q' →
    hAX owned_next
      (state_sat fun c => asep (state_obligation .child Q c) (state_obligation .parent Q' c))
      (init_owned child (k ()) h h' ctx base) →
    hAX owned_next Q (init_local .child child h ctx base false) ∧
    hAX owned_next Q' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HQ HQ' HsQ HsQ' HX
  obtain ⟨HC, HPa⟩ := global_hax_split Q Q' _ (coupled_init _ _ _ _ _ _ Hadm)
    HQ HQ' (init_project_size ..) (init_project_size ..) HsQ HsQ' HX
  rw [owned_equ_eq (project_init_child ..)] at HC
  rw [owned_equ_eq (project_init_parent ..)] at HPa
  exact ⟨HC, HPa⟩

theorem fork_hag_split (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (I : hprop) (rankC rankP : OwnedCfg → Nat) (P P' : hprop) :
    admissible child (k ()) h h' ctx base →
    hproper P → hproper P' →
    I (init_owned child (k ()) h h' ctx base) → step_closed I →
    finite_release .child I rankC → finite_release .parent I rankP →
    hAG owned_next
      (state_sat fun c => asep (state_obligation .child P c) (state_obligation .parent P' c))
      (init_owned child (k ()) h h' ctx base) →
    hAG owned_next P (init_local .child child h ctx base true) ∧
    hAG owned_next P' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HP HP' HI Hcl HrC HrP HG
  obtain ⟨HC, HPa⟩ := global_hag_split I rankC rankP P P' _ (coupled_init _ _ _ _ _ _ Hadm)
    HP HP' HI Hcl HrC HrP HG
  rw [owned_equ_eq (project_init_child ..)] at HC
  rw [owned_equ_eq (project_init_parent ..)] at HPa
  exact ⟨hAG_select_strip _ _ _ _ _ _ HC, HPa⟩

theorem fork_heg_fair_split (child : CProg Unit) (k : Unit → CProg Unit) (h h' : ManagedHeap)
    (ctx : Ctx) (base : Nat) (P P' : hprop) (e : Execution OwnedCfg OwnedAction Unit) :
    admissible child (k ()) h h' ctx base →
    hproper P → hproper P' →
    e.states 0 = init_owned child (k ()) h h' ctx base → owned_run e →
    (∀ n, state_sat (fun c => asep (state_obligation .child P c)
      (state_obligation .parent P' c)) (e.states n)) →
    infinitely (fun n => (e.selected n).owner = .child) →
    infinitely (fun n => (e.selected n).owner = .parent) →
    hEG owned_next P (init_local .child child h ctx base true) ∧
    hEG owned_next P' (init_local .parent (k ()) h' ctx base true) := by
  intro Hadm HP HP' H0 Hrun Hsep HinfC HinfP
  obtain ⟨HC, HPa⟩ := global_heg_fair_split P P' _ e (coupled_init _ _ _ _ _ _ Hadm)
    HP HP' H0 Hrun Hsep HinfC HinfP
  rw [owned_equ_eq (project_init_child ..)] at HC
  rw [owned_equ_eq (project_init_parent ..)] at HPa
  obtain ⟨-, c', ⟨a, Hst⟩, HE⟩ := (hEG_unfold _ _ _).1 HC
  obtain ⟨-, rfl⟩ := (init_local_select _ _ _ _ _ _ _).1 Hst
  exact ⟨HE, HPa⟩

/-! ## Original TICL judgments and the erased action clock -/

/-- Extensional heap equivalence determines the concrete target return. -/
theorem owned_result_rel_right_unique :
    ∀ (r r1 r2 : PUnit × SSig), owned_result_rel r r1 → owned_result_rel r r2 → r1 = r2 := by
  rintro ⟨x, ⟨h, al⟩, aux⟩ ⟨x1, ⟨h1, al1⟩, aux1⟩ ⟨x2, ⟨h2, al2⟩, aux2⟩
    ⟨rfl, rfl, Hh1, Hal1⟩ ⟨rfl, rfl, Hh2, Hal2⟩
  have Hh : h1 = h2 := funext fun a => (Hh1 a).symm.trans (Hh2 a)
  have Hal : al1 = al2 := funext fun a => (Hal1 a).symm.trans (Hal2 a)
  subst Hh Hal
  rfl

-- Not ported: `weak_project_sim_l`, `weak_project_sim_r`, `weak_project_atom` (Rocq `Local`
-- simulation helpers for `sim_anc`/…; the `weak_h*_to_local` proofs use the `hAN_iff`/`hAU_ind`/
-- `hAG_coind` API directly, `owned_equ` being `=`).

end CoCSL
