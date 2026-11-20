/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Separation.FiniteRegression

/-!
# Original-TICL bridge regressions: the owned and raw clocks differ

The finite owned AF/EF results of `FiniteRegression` transport to the raw nondeterministic
runner; at the terminal owned state no owned action remains, yet the raw tree still takes its
value transition (← `examples/CSL/Frame/Separation.v`, module `FiniteTiclRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation.FiniteTiclRegression
open CTree Tisl Tisl.Heap Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Separation.FiniteRegression

def final_cells (r : PUnit × SSig) : Prop :=
  (csl_memory r.2).1 1 = some 1 ∧ (csl_memory r.2).1 2 = some 8

theorem final_cells_proper (r r' : PUnit × SSig) :
    owned_result_rel r r' → (final_cells r ↔ final_cells r') := by
  obtain ⟨x, s⟩ := r; obtain ⟨x', s'⟩ := r'
  rintro ⟨-, -, HD, -⟩
  simp only [final_cells, HD 1, HD 2]

theorem separated_done_joined (d : OwnedCfg) :
    state_sat (fun c => asep (state_obligation .child done_C c)
      (state_obligation .parent done_P c)) d →
    hDone (fun d => final_cells (PUnit.unit, joined_state d)) d := by
  intro HI
  obtain ⟨W, ⟨HCt, HC⟩, ⟨HPt, HP⟩⟩ := (state_split_iff _ _ _).1 HI
  refine ⟨?_, ?_, ?_⟩
  · have := project_size_partition d
    unfold terminal at HCt HPt ⊢
    omega
  · change (d.heap .child).1 1 = some 1 at HC
    show (joined_heap d).1 1 = some 1
    rw [joined_lookup d .child 1 W (W.2.2.2.2.2.1.1 1 (by rw [HC]; simp)), HC]
  · change (d.heap .parent).1 2 = some 8 at HP
    show (joined_heap d).1 2 = some 8
    rw [joined_lookup d .parent 2 W (W.2.2.2.2.2.2.1.1 2 (by rw [HP]; simp)), HP]

theorem finite_owned_haf :
    hAF owned_next (hDone fun d => final_cells (PUnit.unit, joined_state d)) s0 :=
  hAU_mono _ _ _ _ _ s0 (fun _ _ => trivial) separated_done_joined fglobal_hau

theorem finite_owned_hef :
    hEF owned_next (hDone fun d => final_cells (PUnit.unit, joined_state d)) s0 :=
  hEU_mono _ _ _ _ _ s0 (fun _ _ => trivial) separated_done_joined fglobal_heu

theorem finite_raw_af_done :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (fun r _ => final_cells r) wd)
      (run_nd (.bind (.fork fchild) fk) (hC ⊎ hP, (ctx0, 0))) .pure :=
  fork_haf_done_ticl fchild fk hC hP ctx0 0 final_cells fadmissible final_cells_proper
    finite_owned_haf

theorem finite_raw_ef_done :
    Euc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (fun r _ => final_cells r) wd)
      (run_nd (.bind (.fork fchild) fk) (hC ⊎ hP, (ctx0, 0))) .pure :=
  fork_hef_done_ticl fchild fk hC hP ctx0 0 final_cells fadmissible final_cells_proper
    finite_owned_hef

theorem det_erasable (s : OwnedCfg) (a : OwnedAction) (s' : OwnedCfg) :
    det_act s a s' → erasable s → erasable s' :=
  fun ⟨⟨d, Hs, E⟩, _⟩ H => erasable_equ d s' E (erasable_step s a d H Hs)

theorem finite_terminal_erasable : erasable s9 :=
  det_erasable _ _ _ det89 <| det_erasable _ _ _ det78 <| det_erasable _ _ _ det67 <|
    det_erasable _ _ _ det56 <| det_erasable _ _ _ det45 <| det_erasable _ _ _ det34 <|
    det_erasable _ _ _ det23 <| det_erasable _ _ _ det12 <| det_erasable _ _ _ det01 <|
    admissible_erasable _ _ _ _ _ _ fadmissible

theorem terminal_zero_owned_actions : terminal s9 ∧ ¬ hcan_step owned_next s9 :=
  ⟨rfl, fun ⟨_, _, Hs⟩ => Hs⟩

theorem terminal_raw_value_transition :
    ∃ T, ktrans (owned_interp s9) .pure T (.done (PUnit.unit, joined_state s9)) ∧
      T ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  obtain ⟨T, Ht, Hs⟩ :=
    owned_interp_terminal_trans s9 s9 finite_terminal_erasable .refl rfl
  exact ⟨T, .done _ Ht, Hs⟩

theorem terminal_not_raw_done :
    ¬ DoneWith (E := writerE (CSLObs (Nat × Nat)))
      (fun (r : PUnit × SSig) _ => final_cells r) .pure :=
  nofun

theorem terminal_raw_af_done :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (fun r _ => final_cells r) wd)
      (owned_interp s9) .pure :=
  owned_haf_done_ticl final_cells s9 .pure finite_terminal_erasable .pure final_cells_proper
    (hAU_now _ _ _ s9 ⟨rfl, rfl, rfl⟩)

end Examples.CSL.Frame.Separation.FiniteTiclRegression
