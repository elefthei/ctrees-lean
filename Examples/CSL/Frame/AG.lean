/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Asep

/-!
# Regression: two cooperative loops never fault and never stop

`fork2 (lproc 1) (lproc 2)`: each process loops forever on its own cell. Both schedulers compose
framed finite turns directly with the pool invariant. The contract is `AG ⊤`, including
starvation; no fairness premise is required (← `examples/CSL/Frame/AG.v`).
-/

@[expose] public section
namespace Examples.CSL.Frame.AG
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared Examples.CSL.Frame.Asep

/-- The exact source turns already establish closure of this shared pool. Pool invariance
supplies the infinite safety argument, without recording intermediate thread shapes. -/
theorem ag_two_procs_rr (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AG ⊤) (run_rr (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_rr_fork_bind _ _ _)).2 ?_
  rw [InvariantSeparation.fork2_lprocs_pool]
  exact ag_csl_rr_invariance _ (InvariantSeparation.loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (InvariantSeparation.loop_ranked ctx 0))
    (fun _ _ _ Hw _ => ticll_top Hw) (fun _ _ _ _ _ _ Hw => ticll_top Hw) (a, b, c) _
    (some parent) 0 _ ⟨(InvariantSeparation.split_cells_iff_both _ _ _).2 (peq_refl _), rfl⟩
    .pure

/-- Pool safety does not require fair selection of either component. -/
theorem ag_two_procs_nd (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AG ⊤) (run_nd (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_nd_fork_bind _ _ _)).2 ?_
  rw [InvariantSeparation.fork2_lprocs_pool]
  exact ag_csl_nd_invariance _ (InvariantSeparation.loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (InvariantSeparation.loop_ranked ctx 0))
    (fun _ _ _ Hw _ => ticll_top Hw) (fun _ _ _ _ _ Hw => ticll_top Hw) (a, b, c) _
    (some parent) _ ⟨(InvariantSeparation.split_cells_iff_both _ _ _).2 (peq_refl _), rfl⟩
    .pure

/-- Instantiate round-robin loop safety with concrete initial cell values. -/
theorem ag_rr_3_5 (ctx : Ctx) :
    entails (AG ⊤) (run_rr (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)) .pure :=
  ag_two_procs_rr 3 5 ctx 0

/-- Instantiate nondeterministic loop safety with concrete initial cell values. -/
theorem ag_nd_3_5 (ctx : Ctx) :
    entails (AG ⊤) (run_nd (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)) .pure :=
  ag_two_procs_nd 3 5 ctx 0

#print axioms ag_two_procs_rr
#print axioms ag_two_procs_nd

end Examples.CSL.Frame.AG
