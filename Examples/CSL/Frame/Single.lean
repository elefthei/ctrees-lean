/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Shared

/-!
# Regression: the heap frame rule on a single CSL process

`p` reads cell `1` and writes back its successor. The property is proved on the one-cell heap,
then transported by the frame rule to the heap extended by the disjoint cell `2`; the framed
postcondition still exposes the untouched frame. The negative check shows allocation is not
framable, and the prefix check frames an `AG` of the emit loop
(← `examples/CSL/Frame/Single.v`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Single
open CTree Tisl Tisl.Heap Tisl.Pcm Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared
open ITree (Effect)

/-- Read cell `1` and write its successor. -/
def p : CProg Unit := .bind (.read 1) fun v => .write 1 (v + 1)

/-- Initial state with cell `1` owned and no shared heap. -/
def s0 (ctx : Ctx) : SSig := ((hsingle 1 0, hemp), (ctx, 0))

/-- Disjoint region containing the untouched cell `2`. -/
def fr : ManagedHeap := (hsingle 2 7, hemp)

/-- Rewrite the runner by one `~` step at the goal's tree. -/
local macro "nd_by " t:term : tactic =>
  `(tactic| (refine (proper_entails_meq _ $t).2 ?_; try dsimp only))

/-- The standalone run: cell `1` ends at `1`. -/
theorem p_af_ret (ctx : Ctx) :
    entails (AF (.ret fun (x : PUnit × SSig) _ => (csl_memory x.2).1 1 = some 1))
      (run_nd p (s0 ctx)) .pure := by
  rw [run_nd_focus, p, interp_nd_source_bind]
  nd_by interp_nd_source_read_value 0 _ 0 1 0 _ _ _ ctx 0 rfl
  nd_by interp_nd_source_write_present 0 _ 0 1 _ _ _ _ ctx 0 (by simp [hsingle])
  refine af_log .pure ?_
  nd_by sbisim_trans (interp_schedule_nd_ret sh 0 _ 0 _ rfl) (interp_schedule_nd_empty sh _ _)
  exact .matchA (ret_ret (.obs _ _) rfl)

/-- Preserve the terminal-world property, including the final value transition. -/
theorem p_af (ctx : Ctx) :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (X := PUnit × SSig) (fun x _ => (csl_memory x.2).1 1 = some 1) wd)
      (run_nd p (s0 ctx)) .pure :=
  af_ret_done _ (p_af_ret ctx)

/-- The initial state admits the disjoint frame `fr`. -/
theorem frame_inv_s0 (ctx : Ctx) : frame_inv fr (s0 ctx) :=
  region_frame_inv 1 2 0 7 ctx 0 (by decide)

/-- The framed run on the two-cell heap: cell `1` ends at `1` and cell `2` is still `7`. -/
theorem p_af_framed (ctx : Ctx) :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (X := PUnit × SSig)
        (fun x _ => (csl_memory x.2).1 1 = some 1 ∧ (csl_memory x.2).1 2 = some 7) wd)
      (run_nd p (frame_state fr (s0 ctx))) .pure := by
  apply af_ret_done
  refine aur_ret_mono _ _ _
    (frame_post fr fun (x : PUnit × SSig) _ => (csl_memory x.2).1 1 = some 1) _ ?_ ?_
  · rintro ⟨u, M, aux⟩ w HP
    obtain ⟨m, -, HD, -, HE, -, HP⟩ := (frame_post_iff fr _ M aux u w).1 HP
    refine ⟨(HE.1 1).trans (hunion_some _ _ _ _ HP), (HE.1 2).trans ?_⟩
    rcases HD.1 2 with H0 | H0
    · exact (hunion_none _ _ _ H0).trans rfl
    · exact absurd H0 (by simp [fr, hsingle])
  · have H := run_nd_csl_frame (b := true) fr p (s0 ctx) (frame_state fr (s0 ctx)) _ .pure .pure
      ⟨trivial, fun _ => trivial⟩ (frame_rel_state fr _ (frame_inv_s0 ctx)) .pure (p_af_ret ctx)
    exact auc_mono_l (fun _ _ h => ⟨trivial, h.2⟩) _ _ H

/-- Allocation is not framable. -/
example : ¬ Framable no_alloc_sE (heap_alloc (E := sE) (B := Bn) 1) := by
  intro H
  have H := (framable_unfold _ _).1 H
  simp only [heap_alloc, CTree.trigger', CTree.vis', unfold_vis] at H
  cases H with | vis _ _ h _ => exact h

/-- Prefix frame: the emit loop never stops on the framed heap either. -/
theorem emit_loop_ag_framed (ctx : Ctx) :
    entails (AG (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (run_nd (.untilNone (.bind (.emit 1 2) fun _ => .ret (some ())))
        (frame_state fr (s0 ctx))) .pure :=
  ticl_csl_frame_stable fr _ (s0 ctx) _
    (run_nd_framable (.untilNone (.bind (.emit 1 2) fun _ => .ret (some ())))
      ⟨trivial, fun _ => trivial⟩)
    (frame_rel_state fr _ (frame_inv_s0 ctx)) _ .pure .pure (fun _ _ _ _ _ => trivial) .pure
    (run_nd_emit_loop_ag 1 2 _ ctx 0 .pure .pure)

#print axioms p_af_framed

end Examples.CSL.Frame.Single
