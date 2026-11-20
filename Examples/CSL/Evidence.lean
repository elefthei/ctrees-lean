/- SPDX-License-Identifier: MIT -/
module

import Logic
import Lang
import Examples.HiddenBr
import Examples.CSL.Queue
import Examples.CSL.Control
import Examples.CSL.Frame.AF
import Examples.CSL.Frame.AG
import Examples.CSL.Frame.AN
import Examples.CSL.Frame.Asep
import Examples.CSL.Allocator.Execution
import Examples.CSL.Allocator.Liveness
import Examples.CSL.Allocator.Counterexamples
import Examples.CSL.Frame.HeapObservations
import Examples.CSL.Frame.Separation
import Examples.CSL.Frame.Active

/-!
# Formal-evidence roots (<- `examples/CSL/Evidence.v`)

Each proof root has a `#check` and `#print axioms` pair. Every root must depend only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

#check @Tisl.CSL.csim_interp_frame
#print axioms Tisl.CSL.csim_interp_frame

#check @Tisl.CSL.ticl_csl_frame
#print axioms Tisl.CSL.ticl_csl_frame

#check @Tisl.CSL.ticl_csl_frameW
#print axioms Tisl.CSL.ticl_csl_frameW

#check @Tisl.CSL.anr_csl_frame_done
#print axioms Tisl.CSL.anr_csl_frame_done

#check @Tisl.CSL.aur_csl_frame_done
#print axioms Tisl.CSL.aur_csl_frame_done

#check @Tisl.Yield.rr_fair
#print axioms Tisl.Yield.rr_fair

#check @Tisl.Yield.nd_not_fair
#print axioms Tisl.Yield.nd_not_fair

#check @Tisl.Yield.agaf_pool_fair
#print axioms Tisl.Yield.agaf_pool_fair

#check @Tisl.Yield.agaf_pool_simulation_fair
#print axioms Tisl.Yield.agaf_pool_simulation_fair

#check @Tisl.Yield.pool_simulation_rr_bisim
#print axioms Tisl.Yield.pool_simulation_rr_bisim

#check @Tisl.Yield.source_execution_complete
#print axioms Tisl.Yield.source_execution_complete

#check @Examples.CSL.Queue.Shared.exact_worker_turn
#print axioms Examples.CSL.Queue.Shared.exact_worker_turn

#check @Examples.CSL.Queue.Shared.shared_worker_turn
#print axioms Examples.CSL.Queue.Shared.shared_worker_turn

#check @Examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_nd_fresh
#print axioms Examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_nd_fresh

#check @Examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_rr_fresh
#print axioms Examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_rr_fresh

#check @Examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_fresh
#print axioms Examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_fresh

#check @Examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_q2_fresh
#print axioms Examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_q2_fresh

#check @Examples.CSL.Queue.Client.allocated_shared_queue_passive_fresh_rr
#print axioms Examples.CSL.Queue.Client.allocated_shared_queue_passive_fresh_rr

#check @Examples.CSL.Queue.Client.allocated_shared_queue_split_passive_fresh_rr
#print axioms Examples.CSL.Queue.Client.allocated_shared_queue_split_passive_fresh_rr

#check @Examples.CSL.Queue.Client.allocated_shared_queue_rr_contract
#print axioms Examples.CSL.Queue.Client.allocated_shared_queue_rr_contract

#check @Examples.CSL.Queue.Client.rotate_once_split_cps
#print axioms Examples.CSL.Queue.Client.rotate_once_split_cps

#check @Examples.CSL.Queue.Client.denote_flow_worker_split
#print axioms Examples.CSL.Queue.Client.denote_flow_worker_split

#check @Examples.CSL.Queue.Client.denote_worker_split
#print axioms Examples.CSL.Queue.Client.denote_worker_split

#check @Examples.CSL.Queue.Client.worker_split_pool_rr
#print axioms Examples.CSL.Queue.Client.worker_split_pool_rr

#check @Examples.CSL.Queue.Client.shared_queue_split_rr
#print axioms Examples.CSL.Queue.Client.shared_queue_split_rr

#check @Examples.CSL.Queue.Client.allocated_shared_queue_split_rr
#print axioms Examples.CSL.Queue.Client.allocated_shared_queue_split_rr

#check @Examples.CSL.Queue.Client.client_passive_10
#print axioms Examples.CSL.Queue.Client.client_passive_10

#check @Examples.CSL.Queue.Client.client_split_passive_10
#print axioms Examples.CSL.Queue.Client.client_split_passive_10

#check @Examples.CSL.Queue.Client.client_split_prefix3
#print axioms Examples.CSL.Queue.Client.client_split_prefix3

#check @Examples.CSL.Queue.Client.client_frame_preserved
#print axioms Examples.CSL.Queue.Client.client_frame_preserved

#check @Examples.CSL.Queue.Client.client_heap_cycle3
#print axioms Examples.CSL.Queue.Client.client_heap_cycle3

#check @Tisl.af_vis_eventually_label
#print axioms Tisl.af_vis_eventually_label

#check @Tisl.agaf_family_recurrent_label
#print axioms Tisl.agaf_family_recurrent_label

#check @Tisl.CSL.csl_fresh_implies_recurrent_emission
#print axioms Tisl.CSL.csl_fresh_implies_recurrent_emission

#check @Examples.CSL.Frame.HeapObservations.EventRecurrenceControls.repeat_plain_payload_recurrent
#print axioms
  Examples.CSL.Frame.HeapObservations.EventRecurrenceControls.repeat_plain_payload_recurrent

#check @Examples.CSL.Frame.HeapObservations.EventRecurrenceControls.retained_payload_not_recurrent
#print axioms
  Examples.CSL.Frame.HeapObservations.EventRecurrenceControls.retained_payload_not_recurrent

open Examples.CSL.Frame.HeapObservations in
#check @EventRecurrenceControls.universal_recurrence_rejects_silent_branch
open Examples.CSL.Frame.HeapObservations in
#print axioms EventRecurrenceControls.universal_recurrence_rejects_silent_branch

#check @Examples.CSL.Frame.HeapObservations.EventRecurrenceControls.event_recurrence_rejects_return
#print axioms
  Examples.CSL.Frame.HeapObservations.EventRecurrenceControls.event_recurrence_rejects_return


#check @Examples.CSL.Frame.Shared.write_ax_ret
#print axioms Examples.CSL.Frame.Shared.write_ax_ret

#check @Examples.CSL.Frame.Shared.write_ax_done_framed
#print axioms Examples.CSL.Frame.Shared.write_ax_done_framed

#check @Examples.CSL.Frame.AN.an_two_procs_nd
#print axioms Examples.CSL.Frame.AN.an_two_procs_nd

#check @Examples.CSL.Frame.AN.an_two_procs_rr
#print axioms Examples.CSL.Frame.AN.an_two_procs_rr

#check @Examples.CSL.Frame.AN.wproc_own_2_no_ax6_nd
#print axioms Examples.CSL.Frame.AN.wproc_own_2_no_ax6_nd

#check @Examples.CSL.Control.captured_before_yield_rr
#print axioms Examples.CSL.Control.captured_before_yield_rr

#check @Examples.HiddenBr.delayed_branch_permutation
#print axioms Examples.HiddenBr.delayed_branch_permutation

#check @Examples.HiddenBr.refine_rr_branch01_zero
#print axioms Examples.HiddenBr.refine_rr_branch01_zero

#check @Examples.HiddenBr.refine_rr_branch10_zero
#print axioms Examples.HiddenBr.refine_rr_branch10_zero

#check @Examples.HiddenBr.refine_rr_not_sbisim_congruent
#print axioms Examples.HiddenBr.refine_rr_not_sbisim_congruent

#check @Examples.HiddenBr.rr_preserves_thread_branch
#print axioms Examples.HiddenBr.rr_preserves_thread_branch

#check @Examples.CSL.Allocator.Execution.allocator_simulation
#print axioms Examples.CSL.Allocator.Execution.allocator_simulation

#check @Examples.CSL.Allocator.Liveness.allocator_agaf_fair
#print axioms Examples.CSL.Allocator.Liveness.allocator_agaf_fair

#check @Examples.CSL.Allocator.Liveness.source_remote_free_lockfree
#print axioms Examples.CSL.Allocator.Liveness.source_remote_free_lockfree

#check @Examples.CSL.Allocator.Liveness.source_retired_eventually_reclaimed
#print axioms Examples.CSL.Allocator.Liveness.source_retired_eventually_reclaimed

#check @Examples.CSL.Allocator.Counterexamples.fair_starvation_exists
#print axioms Examples.CSL.Allocator.Counterexamples.fair_starvation_exists

#check @Examples.CSL.Allocator.Counterexamples.owner_stall_prevents_reclamation
#print axioms Examples.CSL.Allocator.Counterexamples.owner_stall_prevents_reclamation

#check @Tisl.ticll_sim
#print axioms Tisl.ticll_sim

#check @Tisl.ticl_sim
#print axioms Tisl.ticl_sim

#check @Tisl.Yield.interp_schedule_fair_user_bind
#print axioms Tisl.Yield.interp_schedule_fair_user_bind

#check @CoCSL.run_rr_fork_bind
#print axioms CoCSL.run_rr_fork_bind

#check @Tisl.proper_entails_meq
#print axioms Tisl.proper_entails_meq

#check @Tisl.ag_iter
#print axioms Tisl.ag_iter

#check @Tisl.u_bind_r
#print axioms Tisl.u_bind_r

#check @Tisl.soundness
#print axioms Tisl.soundness

#check @Tisl.an_step
#print axioms Tisl.an_step

#check @Tisl.au_state_bind_r
#print axioms Tisl.au_state_bind_r

#check @Tisl.CSL.prim_reflect_joined
#print axioms Tisl.CSL.prim_reflect_joined

#check @CoCSL.owned_fork_runner
#print axioms CoCSL.owned_fork_runner

#check @Tisl.CSL.owned_interp_action
#print axioms Tisl.CSL.owned_interp_action

#check @CoCSL.global_hau_split
#print axioms CoCSL.global_hau_split

#check @CoCSL.global_heu_split
#print axioms CoCSL.global_heu_split

#check @CoCSL.global_han_split
#print axioms CoCSL.global_han_split

#check @CoCSL.global_hag_split
#print axioms CoCSL.global_hag_split

#check @CoCSL.global_heg_fair_split
#print axioms CoCSL.global_heg_fair_split

#check @CoCSL.global_heg_fair_one
#print axioms CoCSL.global_heg_fair_one

#check @CoCSL.global_hdone_split
#print axioms CoCSL.global_hdone_split

#check @CoCSL.global_hret_split
#print axioms CoCSL.global_hret_split

#check @Tisl.CSL.same_view_equivalence
#print axioms Tisl.CSL.same_view_equivalence

#check @Tisl.CSL.owned_equ_same_view
#print axioms Tisl.CSL.owned_equ_same_view

#check @Tisl.CSL.same_view_project
#print axioms Tisl.CSL.same_view_project

#check @Examples.CSL.Frame.Separation.NextRegression.unequal_lineage_counts_not_uniform
#print axioms Examples.CSL.Frame.Separation.NextRegression.unequal_lineage_counts_not_uniform

#check @CoCSL.global_han_owned
#print axioms CoCSL.global_han_owned

#check @CoCSL.global_hen_owned
#print axioms CoCSL.global_hen_owned

#check @CoCSL.weak_han_to_local
#print axioms CoCSL.weak_han_to_local

#check @CoCSL.weak_hen_to_local
#print axioms CoCSL.weak_hen_to_local

#check @CoCSL.weak_hau_to_local
#print axioms CoCSL.weak_hau_to_local

#check @CoCSL.weak_heu_to_local
#print axioms CoCSL.weak_heu_to_local

#check @CoCSL.weak_hag_to_local
#print axioms CoCSL.weak_hag_to_local

#check @CoCSL.weak_heg_to_local
#print axioms CoCSL.weak_heg_to_local

#check @CoCSL.weak_hret_to_local
#print axioms CoCSL.weak_hret_to_local

#check @CoCSL.fork_hau_split
#print axioms CoCSL.fork_hau_split

#check @CoCSL.fork_heu_split
#print axioms CoCSL.fork_heu_split

#check @CoCSL.fork_hau_split_view
#print axioms CoCSL.fork_hau_split_view

#check @CoCSL.fork_han_split
#print axioms CoCSL.fork_han_split

#check @CoCSL.fork_hag_split
#print axioms CoCSL.fork_hag_split

#check @CoCSL.fork_heg_fair_split
#print axioms CoCSL.fork_heg_fair_split

#check @Examples.CSL.Frame.Separation.FiniteRegression.fork_run_nd_trace
#print axioms Examples.CSL.Frame.Separation.FiniteRegression.fork_run_nd_trace

#check @Tisl.sbisim_csim
#print axioms Tisl.sbisim_csim

#check @Tisl.CSL.owned_interp_trans_forward
#print axioms Tisl.CSL.owned_interp_trans_forward

#check @Tisl.CSL.owned_interp_visible
#print axioms Tisl.CSL.owned_interp_visible

#check @Tisl.CSL.owned_interp_terminal_trans
#print axioms Tisl.CSL.owned_interp_terminal_trans

#check @Tisl.CSL.owned_interp_silent
#print axioms Tisl.CSL.owned_interp_silent

#check @Tisl.CSL.owned_interp_select
#print axioms Tisl.CSL.owned_interp_select

#check @Tisl.CSL.owned_interp_terminal
#print axioms Tisl.CSL.owned_interp_terminal

#check @CoCSL.owned_ticl_transport
#print axioms CoCSL.owned_ticl_transport

#check @CoCSL.fork_ticl
#print axioms CoCSL.fork_ticl

#check @CoCSL.owned_haf_done_ticl
#print axioms CoCSL.owned_haf_done_ticl

#check @CoCSL.owned_hef_done_ticl
#print axioms CoCSL.owned_hef_done_ticl

#check @CoCSL.owned_hag_ticl
#print axioms CoCSL.owned_hag_ticl

#check @CoCSL.owned_heg_ticl
#print axioms CoCSL.owned_heg_ticl

#check @CoCSL.fork_haf_done_ticl
#print axioms CoCSL.fork_haf_done_ticl

#check @CoCSL.fork_hef_done_ticl
#print axioms CoCSL.fork_hef_done_ticl

#check @CoCSL.fork_hag_ticl
#print axioms CoCSL.fork_hag_ticl

#check @CoCSL.fork_heg_ticl
#print axioms CoCSL.fork_heg_ticl

#check @Examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_af_done
#print axioms Examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_af_done

#check @Examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_ef_done
#print axioms Examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_ef_done

#check @Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_zero_owned_actions
#print axioms Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_zero_owned_actions

#check @Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_value_transition
#print axioms Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_value_transition

#check @Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_not_raw_done
#print axioms Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_not_raw_done

#check @Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_af_done
#print axioms Examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_af_done

#check @Examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_ag
#print axioms Examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_ag

#check @Examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_eg
#print axioms Examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_eg

#check @Examples.CSL.Frame.Separation.AlwaysTiclRegression.fair_exec_infinitely_visible
#print axioms Examples.CSL.Frame.Separation.AlwaysTiclRegression.fair_exec_infinitely_visible

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_admissible
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_admissible

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_owned_hag
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_owned_hag

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_focused_owned_hag
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_focused_owned_hag

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_stuck
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_stuck

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_no_ag
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_no_ag

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_stuck
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_stuck

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_no_ag
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_no_ag

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_run
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_run

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_infinitely_reads
#print axioms Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_infinitely_reads

#check @Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_not_infinitely_visible
#print axioms
  Examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_not_infinitely_visible

#check @Examples.CSL.Frame.AF.af_two_procs_rr
#print axioms Examples.CSL.Frame.AF.af_two_procs_rr

#check @Examples.CSL.Frame.AF.af_two_procs_nd
#print axioms Examples.CSL.Frame.AF.af_two_procs_nd

#check @Examples.CSL.Frame.AG.ag_two_procs_rr
#print axioms Examples.CSL.Frame.AG.ag_two_procs_rr

#check @Examples.CSL.Frame.AG.ag_two_procs_nd
#print axioms Examples.CSL.Frame.AG.ag_two_procs_nd

#check @Tisl.map_atoms
#print axioms Tisl.map_atoms

#check @Tisl.framer_event_eq
#print axioms Tisl.framer_event_eq

#check @Tisl.CSL.frameER_right_unique
#print axioms Tisl.CSL.frameER_right_unique

#check @Tisl.ag_state_iter_logs
#print axioms Tisl.ag_state_iter_logs

#check @Tisl.realizes_emit_list_prefix
#print axioms Tisl.realizes_emit_list_prefix

#check @Tisl.heap_handlerW_alloc_no_space
#print axioms Tisl.heap_handlerW_alloc_no_space

#check @Examples.CSL.Frame.Shared.write_ax_ret_framed
#print axioms Examples.CSL.Frame.Shared.write_ax_ret_framed

#check @Examples.CSL.Frame.AN.an_two_procs_nd_ret
#print axioms Examples.CSL.Frame.AN.an_two_procs_nd_ret

#check @Examples.CSL.Frame.AN.an_two_procs_rr_ret
#print axioms Examples.CSL.Frame.AN.an_two_procs_rr_ret

#check @Examples.CSL.Frame.AN.an_rr_3_5
#print axioms Examples.CSL.Frame.AN.an_rr_3_5

#check @Examples.CSL.Frame.AN.an_nd_3_5
#print axioms Examples.CSL.Frame.AN.an_nd_3_5

#check @Examples.CSL.Frame.HeapObservations.mutation_probe_spec
#print axioms Examples.CSL.Frame.HeapObservations.mutation_probe_spec

#check @Examples.CSL.Frame.HeapObservations.same_value_mutations_visible
#print axioms Examples.CSL.Frame.HeapObservations.same_value_mutations_visible

#check @Examples.CSL.Frame.HeapObservations.fault_prefix_preserved
#print axioms Examples.CSL.Frame.HeapObservations.fault_prefix_preserved

#check @Examples.CSL.Frame.HeapObservations.mutation_loop_prefix_nd
#print axioms Examples.CSL.Frame.HeapObservations.mutation_loop_prefix_nd

#check @Examples.CSL.Frame.HeapObservations.mutation_loop_prefix_rr
#print axioms Examples.CSL.Frame.HeapObservations.mutation_loop_prefix_rr

#check @Examples.CSL.Frame.HeapObservations.mutation_loop_agaf_nd
#print axioms Examples.CSL.Frame.HeapObservations.mutation_loop_agaf_nd

#check @Examples.CSL.Frame.HeapObservations.mutation_loop_agaf_rr
#print axioms Examples.CSL.Frame.HeapObservations.mutation_loop_agaf_rr

#check @Examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_nd
#print axioms Examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_nd

#check @Examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_rr
#print axioms Examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_rr

#check @Examples.CSL.Frame.HeapObservations.mutation_observation_replaced
#print axioms Examples.CSL.Frame.HeapObservations.mutation_observation_replaced

#check @Examples.CSL.Frame.HeapObservations.mutation_loop_framed_nd
#print axioms Examples.CSL.Frame.HeapObservations.mutation_loop_framed_nd

#check @Examples.CSL.Frame.HeapObservations.mutation_loop_framed_rr
#print axioms Examples.CSL.Frame.HeapObservations.mutation_loop_framed_rr

#check @Examples.CSL.Frame.HeapObservations.mutation_return_framed
#print axioms Examples.CSL.Frame.HeapObservations.mutation_return_framed

#check @Examples.CSL.Frame.HeapObservations.queue_snapshot_prefix
#print axioms Examples.CSL.Frame.HeapObservations.queue_snapshot_prefix

#check @Examples.CSL.Frame.HeapObservations.allocator_snapshot_prefix
#print axioms Examples.CSL.Frame.HeapObservations.allocator_snapshot_prefix

#check @Examples.CSL.Frame.HeapObservations.allocator_partial_fault_prefix
#print axioms Examples.CSL.Frame.HeapObservations.allocator_partial_fault_prefix

#check @Examples.CSL.Frame.HeapObservations.two_log_iterator_recurrence
#print axioms Examples.CSL.Frame.HeapObservations.two_log_iterator_recurrence

#check @Examples.CSL.Frame.HeapObservations.two_log_detached_suffix_no_target
#print axioms Examples.CSL.Frame.HeapObservations.two_log_detached_suffix_no_target

#check @Examples.CSL.Frame.HeapObservations.empty_log_pool_selection
#print axioms Examples.CSL.Frame.HeapObservations.empty_log_pool_selection

#check @Examples.CSL.Frame.HeapObservations.finish_heap_predecessor_framed
#print axioms Examples.CSL.Frame.HeapObservations.finish_heap_predecessor_framed

#check @Examples.CSL.Frame.HeapObservations.emission_prefix_stable
#print axioms Examples.CSL.Frame.HeapObservations.emission_prefix_stable

#check @Examples.CSL.Frame.HeapObservations.exact_heap_prefix_not_stable
#print axioms Examples.CSL.Frame.HeapObservations.exact_heap_prefix_not_stable

#check @Examples.CSL.Frame.HeapObservations.invalid_and_double_free_prefix
#print axioms Examples.CSL.Frame.HeapObservations.invalid_and_double_free_prefix

#check @Examples.CSL.Frame.HeapObservations.initialization_fault_prefix
#print axioms Examples.CSL.Frame.HeapObservations.initialization_fault_prefix

#check @Examples.CSL.Frame.HeapObservations.allocation_no_space_silent
#print axioms Examples.CSL.Frame.HeapObservations.allocation_no_space_silent

#check @Examples.CSL.Frame.HeapObservations.empty_log_closed_turns
#print axioms Examples.CSL.Frame.HeapObservations.empty_log_closed_turns

#check @Examples.CSL.Frame.HeapObservations.empty_log_pool_invariance_nd_rr
#print axioms Examples.CSL.Frame.HeapObservations.empty_log_pool_invariance_nd_rr

#check @Tisl.CSL.asep_anc_compose
#print axioms Tisl.CSL.asep_anc_compose

#check @Tisl.CSL.asep_enc_compose
#print axioms Tisl.CSL.asep_enc_compose

#check @Tisl.CSL.asep_agc_compose
#print axioms Tisl.CSL.asep_agc_compose

#check @Tisl.CSL.asep_ret_compose
#print axioms Tisl.CSL.asep_ret_compose

#check @Tisl.CSL.asep_auc_ret_compose
#print axioms Tisl.CSL.asep_auc_ret_compose

#check @Tisl.CSL.asep_euc_ret_compose
#print axioms Tisl.CSL.asep_euc_ret_compose

#check @Tisl.CSL.asep_egc_run
#print axioms Tisl.CSL.asep_egc_run

#check @Tisl.CSL.asep_af_ret_compose
#print axioms Tisl.CSL.asep_af_ret_compose

#check @Tisl.CSL.asep_ef_ret_compose
#print axioms Tisl.CSL.asep_ef_ret_compose

#check @Tisl.CSL.asep_sat
#print axioms Tisl.CSL.asep_sat

#check @Tisl.CSL.asep_sat_intro
#print axioms Tisl.CSL.asep_sat_intro

#check @Tisl.CSL.local_obligation_proper
#print axioms Tisl.CSL.local_obligation_proper

#check @Tisl.CSL.asep_ret
#print axioms Tisl.CSL.asep_ret

#check @Tisl.CSL.asep_ret_elim
#print axioms Tisl.CSL.asep_ret_elim

#check @Tisl.egc_of_sequence
#print axioms Tisl.egc_of_sequence

#check @Tisl.CSL.state_split_proper
#print axioms Tisl.CSL.state_split_proper

#check @Tisl.CSL.state_split_iff
#print axioms Tisl.CSL.state_split_iff

#check @Tisl.CSL.state_split_forget
#print axioms Tisl.CSL.state_split_forget

#check @Tisl.CSL.asep_at_inv
#print axioms Tisl.CSL.asep_at_inv

#check @Tisl.CSL.asep_sat_inv
#print axioms Tisl.CSL.asep_sat_inv

#check @Tisl.CSL.asep_local_step_inv
#print axioms Tisl.CSL.asep_local_step_inv

#check @Tisl.CSL.asep_at_auc_ret_step
#print axioms Tisl.CSL.asep_at_auc_ret_step

#check @Tisl.CSL.asep_auc_ret_empty
#print axioms Tisl.CSL.asep_auc_ret_empty

#check @Tisl.CSL.asep_ax_compose
#print axioms Tisl.CSL.asep_ax_compose

#check @Tisl.CSL.asep_ex_compose
#print axioms Tisl.CSL.asep_ex_compose

#check @Examples.CSL.Frame.Active.NativeReturnRegression.native_ret_silent_frontier
#print axioms Examples.CSL.Frame.Active.NativeReturnRegression.native_ret_silent_frontier

#check @Examples.CSL.Frame.Active.OperationalNextRegression.one_write_has_single_owner
#print axioms Examples.CSL.Frame.Active.OperationalNextRegression.one_write_has_single_owner

#check @Examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_AN
#print axioms Examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_AN

#check @Examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_EN
#print axioms Examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_EN

#check @Examples.CSL.Frame.Active.AsyncNextRegression.global_next_retains_failed_target
#print axioms Examples.CSL.Frame.Active.AsyncNextRegression.global_next_retains_failed_target

#check @Examples.CSL.Frame.Active.AsyncNextRegression.global_next_exactly_one_action
#print axioms Examples.CSL.Frame.Active.AsyncNextRegression.global_next_exactly_one_action

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_init
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_init

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_closed
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_closed

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.early_termination_inv
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.early_termination_inv

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_init
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_init

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_closed
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_closed

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.both_af_final_cells
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.both_af_final_cells

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.both_ef_final_cells
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.both_ef_final_cells

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.early_parent_return_phase
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.early_parent_return_phase

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.early_not_live_live
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.early_not_live_live

#check @Examples.CSL.Frame.Active.TerminationActiveRegression.early_until_ret
#print axioms Examples.CSL.Frame.Active.TerminationActiveRegression.early_until_ret

#check @Examples.CSL.Frame.Active.AlwaysActiveRegression.loops_active_ag
#print axioms Examples.CSL.Frame.Active.AlwaysActiveRegression.loops_active_ag

#check @Examples.CSL.Frame.Active.CommonEGActiveRegression.fair_view_exec_valid
#print axioms Examples.CSL.Frame.Active.CommonEGActiveRegression.fair_view_exec_valid

#check @Examples.CSL.Frame.Active.CommonEGActiveRegression.fair_local_assertions
#print axioms Examples.CSL.Frame.Active.CommonEGActiveRegression.fair_local_assertions

#check @Examples.CSL.Frame.Active.CommonEGActiveRegression.common_visible_execution_eg
#print axioms Examples.CSL.Frame.Active.CommonEGActiveRegression.common_visible_execution_eg

#check @Examples.CSL.Frame.Active.CommonEGActiveRegression.silent_reads_are_not_visible_recurrence
#print axioms
  Examples.CSL.Frame.Active.CommonEGActiveRegression.silent_reads_are_not_visible_recurrence

#check @Examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_init
#print axioms Examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_init

#check @Examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_closed
#print axioms Examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_closed

#check @Examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_inv
#print axioms Examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_inv

#check @Examples.CSL.Frame.Active.TransientActiveRegression.phase_view_step
#print axioms Examples.CSL.Frame.Active.TransientActiveRegression.phase_view_step

#check @Examples.CSL.Frame.Active.TransientActiveRegression.parent_progress_remembered
#print axioms Examples.CSL.Frame.Active.TransientActiveRegression.parent_progress_remembered

#check @Examples.CSL.Frame.Active.TransientActiveRegression.child_local_af
#print axioms Examples.CSL.Frame.Active.TransientActiveRegression.child_local_af

#check @Examples.CSL.Frame.Active.TransientActiveRegression.parent_local_af
#print axioms Examples.CSL.Frame.Active.TransientActiveRegression.parent_local_af

#check
  @Examples.CSL.Frame.Active.TransientActiveRegression.no_global_ef_separated_transient_endpoints
#print axioms
  Examples.CSL.Frame.Active.TransientActiveRegression.no_global_ef_separated_transient_endpoints

#check @Examples.CSL.Frame.Active.FaultRegression.invalid_write_stuck
#print axioms Examples.CSL.Frame.Active.FaultRegression.invalid_write_stuck

#check @Examples.CSL.Frame.Active.FaultRegression.invalid_write_not_admissible
#print axioms Examples.CSL.Frame.Active.FaultRegression.invalid_write_not_admissible

/-! Independent actual-shared-run proofs using ordinary `asep`; these eight
    concrete roots do not replace the generic pointwise composition rules. -/
#check @Examples.CSL.Frame.Asep.InvariantSeparation.bind_keeps_parent_post
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.bind_keeps_parent_post

#check @Examples.CSL.Frame.Asep.InvariantSeparation.asep_two_procs_nd_ret
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.asep_two_procs_nd_ret

#check @Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ax2
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ax2

#check @Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_not_ax1
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_not_ax1

#check @Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_child
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_child

#check @Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_parent
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_parent

#check @Examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_nd
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_nd

#check @Examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_rr
#print axioms Examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_rr
