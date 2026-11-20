/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Separation.AlwaysRegression

/-!
# AG/EG of the two-loop fork as original TICL judgments

The phase invariant of `AlwaysRegression`, saturated under `owned_equ`, with the focused phase
rank as raw silence rank, transports the owned `AG` to `AG ⊤` of the nondeterministic runner;
the concrete fair execution, whose emit positions recur, gives `EG ⊤`
(← `examples/CSL/Frame/Separation.v`, module `AlwaysTiclRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation.AlwaysTiclRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.CSL Tisl.Yield Tisl.Notation CoCSL
open Examples.CSL.Frame.Separation.AlwaysRegression

theorem phase_rank_equ (c d : OwnedCfg) :
    owned_equ c d → AlwaysRegression.rank c = AlwaysRegression.rank d :=
  fun E => owned_equ_eq E ▸ rfl

/-- This is the focused phase rank, not either lineage's release rank: selection and emission
already provide raw progress. -/
def raw_silence_rank (d : OwnedCfg) : Nat := AlwaysRegression.rank d

theorem phase_silent_decreases (d : OwnedCfg) (a : OwnedAction) (d' : OwnedCfg) :
    Inv d → owned_step d a d' → erase_action_label a (joined_heap d') = none →
    raw_silence_rank d' < raw_silence_rank d := by
  intro HI Hs He
  obtain ⟨-, Hf | Hr⟩ := Inv_step d a d' HI Hs
  · obtain ⟨-, -, -, tc, tp, f, Hpool, -⟩ := HI
    unfold focused_thread at Hf
    rw [Hpool] at Hf
    rcases f with _ | j
    · unfold owned_step at Hs
      rw [Hpool] at Hs
      obtain ⟨j, rfl, -⟩ := Hs
      cases He
    · cases Hf
  · exact Hr

/-- Saturating the existing phase invariant only makes its setoid properness explicit; its
operational cases are still `Inv_step`. -/
def raw_Inv (d : OwnedCfg) : Prop := ∃ q, Inv q ∧ owned_equ q d

theorem raw_Inv_proper : hproper raw_Inv := fun _ _ E => owned_equ_eq E ▸ Iff.rfl

theorem raw_Inv_silent_decreases (d : OwnedCfg) (a : OwnedAction) (d' : OwnedCfg) :
    raw_Inv d → owned_step d a d' → erase_action_label a (joined_heap d') = none →
    raw_silence_rank d' < raw_silence_rank d := by
  rintro ⟨q, HI, E⟩ Hs He
  obtain rfl := owned_equ_eq E
  exact phase_silent_decreases q a d' HI Hs He

theorem loops_raw_invariant_hag : hAG owned_next raw_Inv c0 :=
  hAG_coind _ _ Inv (fun d HI => ⟨⟨d, HI, owned_equ_Equivalence.refl _⟩, Inv_can d HI,
    fun d' ⟨a, Hs⟩ => Inv_closed d a d' HI Hs⟩) c0 Inv_c0

theorem loops_raw_ag :
    entails (AG (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (run_nd (.bind (.fork pc) fun _ => pp) (hC ⊎ hP, (ctx0, 0))) .pure :=
  fork_hag_ticl pc (fun _ => pp) hC hP ctx0 0 raw_Inv raw_silence_rank loops_admissible
    raw_Inv_proper raw_Inv_silent_decreases loops_raw_invariant_hag

/-- Visibility is proved from this execution's actual emit positions, not from the independent
facts that both owners occur infinitely often. -/
theorem fair_exec_infinitely_visible :
    infinitely (fun n =>
      erase_action_label (fair_exec.selected n) (joined_heap (fair_exec.states (n + 1))) ≠
        none) := by
  intro n
  have H : ∃ k, ∀ d post,
      erase_action_label (act (pos_owner (Nat.repeat next_pos k (run n).1))
        (pos_kind (Nat.repeat next_pos k (run n).1) d)) post ≠ none := by
    cases (run n).1 <;>
      first
        | (refine ⟨0, fun _ _ h => ?_⟩; cases h; done)
        | (refine ⟨1, fun _ _ h => ?_⟩; cases h; done)
        | (refine ⟨2, fun _ _ h => ?_⟩; cases h; done)
        | (refine ⟨3, fun _ _ h => ?_⟩; cases h; done)
  obtain ⟨k, Hk⟩ := H
  refine ⟨n + k, Nat.le_add_right _ _, ?_⟩
  show erase_action_label (act (pos_owner (run (n + k)).1) (pos_kind (run (n + k)).1 _)) _ ≠ none
  rw [run_pos_add n k]
  apply Hk

theorem loops_raw_eg :
    entails (EG (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (run_nd (.bind (.fork pc) fun _ => pp) (hC ⊎ hP, (ctx0, 0))) .pure :=
  fork_heg_ticl pc (fun _ => pp) hC hP ctx0 0 fair_exec loops_admissible rfl fair_exec_spec.2
    fair_exec_infinitely_visible

end Examples.CSL.Frame.Separation.AlwaysTiclRegression
