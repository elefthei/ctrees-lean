/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Sequential
public import Logic.CTree.State
public import Logic.Utils.Relations

/-!
# Recurrence: the heap-backed `AG AF` theorem and its freshness companion

The rotating queue eventually and repeatedly pops every element present in it, over real heap
reads and writes: the outer `AG` by continuation-aware `ag_state_iter_logs`, the inner `AF` by
`u_state_iter_prefix_ghost` with the ghost rank `(kb - counter, first-match position)`. The
occurrence bound `kb` gives the freshness companion. Two controls show the preconditions are
needed (← `examples/CSL/Queue/Recurrence.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Recurrence
open CTree Tisl Tisl.Notation Tisl.Heap Tisl.Ctx Tisl.CSL Examples.CSL.Queue.Representation
  Examples.CSL.Queue.Operations Examples.CSL.Queue.Sequential
open ITree (Effect)

section Recurrence
/- `hdr` is the queue header, `nl` the observed element, `kb` the occurrence bound and `P` any
observation predicate satisfied by every pop of `nl` at or after `kb`. -/
variable (hdr nl kb : Nat) (P : Indexed Nat → Prop) (HP : ∀ j, kb ≤ j → P (stamp nl j))
include HP

/-- The recurrence theorem, generic in the occurrence bound (Rocq `find_index Nat.eqb` is
`find_index Nat.beq`). -/
theorem rotate_agaf_core (h allocs : Heap) (ctx : Ctx) (c : Nat) (ns vs : List Nat) (d : Nat)
    (w : World (writerE (CSLObs Nat))) :
    NotDone w → qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (csl_indexed P))))
      (interp_state (sh (A := Nat)) (rotate hdr) ((h, allocs), (ctx, c))) w := by
  intro Hd Hq Hf
  refine ag_state_iter_logs (sh (A := Nat)) (X := PUnit)
    (fun (_ : PUnit) (s : SSig) => ∃ ns vs d, qrep hdr ns vs s.1.1 ∧
      find_index Nat.beq nl vs = some d)
    (k := fun _ : PUnit => rot_body hdr) (φ := AF (visWₜ (csl_indexed P)))
    ?_ ?_ ?_ ⟨⟩ _ w ⟨ns, vs, d, Hq, Hf⟩ Hd
  · rintro ⟨⟩ ⟨⟨h1, allocs1⟩, ctx1, c1⟩ ⟨ns1, vs1, d1, Hq1, Hf1⟩
    obtain _ | ⟨v1, vs1'⟩ := vs1
    · simp [find_index] at Hf1
    obtain _ | ⟨a1, ns1'⟩ := ns1
    · simpa using qrep_len _ _ _ _ Hq1
    obtain ⟨d', Hd''⟩ := find_index_rotl_pres Nat.beq (fun _ _ => Nat.beq_eq.to_iff) _ _ _ _ Hf1
    exact ⟨⟨⟩, ((rot_heap hdr a1 (ns1'.headD 0) (zof hdr ns1') h1, allocs1), (ctx1, c1 + 1)),
      queue_turn_logs (.emit (stamp v1 c1)) hdr a1 (ns1'.headD 0) ((a1 :: ns1').getLastD 0)
        (h1, allocs1), by simp [queue_turn_logs],
      rot_body_spec hdr a1 ns1' v1 vs1' h1 allocs1 ctx1 c1 Hq1,
      ns1' ++ [a1], vs1' ++ [v1], d', (rot_heap_spec hdr a1 ns1' v1 vs1' h1 Hq1).1, Hd''⟩
  · intro o t w' Hw Hphi
    have Hlog := af_log (k := t) (s := o) Hw Hphi
    rwa [log_vis] at Hlog
  · rintro ⟨⟩ ⟨⟨h1, allocs1⟩, ctx1, c1⟩ w' ⟨ns1, vs1, d1, Hq1, Hf1⟩ Hw
    refine u_state_iter_prefix_ghost (sh (A := Nat)) (q := .A)
      (fun (m : Nat × Nat) (_ : PUnit) (s : SSig) z => NotDone z ∧ ∃ ns vs d,
        qrep hdr ns vs s.1.1 ∧ find_index Nat.beq nl vs = some d ∧
          m = (kb - csl_counter s, d))
      lexnat (k := fun _ : PUnit => rot_body hdr) lexnat_wf ?_ (kb - c1, d1) ⟨⟩ _ w' Hw
      ⟨Hw, ns1, vs1, d1, Hq1, Hf1, rfl⟩
    rintro m ⟨⟩ ⟨⟨h2, allocs2⟩, ctx2, c2⟩ w2 Hd2 ⟨-, ns2, vs2, d2, Hq2, Hf2, Hm⟩
    obtain _ | ⟨v2, vs2'⟩ := vs2
    · simp [find_index] at Hf2
    obtain _ | ⟨a2, ns2'⟩ := ns2
    · simpa using qrep_len _ _ _ _ Hq2
    have Hspec := rot_body_spec hdr a2 ns2' v2 vs2' h2 allocs2 ctx2 c2 Hq2
    obtain ⟨d', Hf', ⟨Hv, Hbound⟩ | Hrank⟩ :=
      find_index_rotation_progress Nat.beq (fun _ _ => Nat.beq_eq.to_iff) nl v2 vs2' d2 Hf2 kb c2
    · left
      refine (proper_entails_meq _ Hspec).2 (af_emit_list_member _ _ w2 _
        (.emit (stamp v2 c2)) Hd2 (by simp [queue_turn_logs]) ?_)
      show P (stamp v2 c2)
      rw [Hv]; exact HP c2 Hbound
    · right
      refine (proper_entails_meq _ Hspec).2 (af_emit_list_ret _ _ w2 _ Hd2
        ⟨(kb - (c2 + 1), d'), ⟨⟩, rfl, after_logs_not_done _ Hd2,
          ⟨after_logs_not_done _ Hd2, ns2' ++ [a2], vs2' ++ [v2], d',
            (rot_heap_spec hdr a2 ns2' v2 vs2' h2 Hq2).1, Hf', rfl⟩, ?_⟩)
      subst Hm
      exact Prod.lex_def.2 Hrank

end Recurrence

/-! ## The two headline theorems -/

/-- The heap-backed counterpart of the reference `rotate_agaf_pop`. -/
theorem rotate_agaf_pop_heap (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (csl_indexed fun o : Indexed Nat => o.value = nl))))
      (run hdr ((h, allocs), (ctx, c))) .pure :=
  fun Hq Hf => rotate_agaf_core hdr nl 0 (fun o => o.value = nl) (fun _ _ => rfl) h allocs ctx c
    ns vs d .pure .pure Hq Hf

/-- Freshness: for every occurrence bound `k`, every reachable state still eventually pops `nl`
with index at least `k`. -/
theorem rotate_agaf_pop_fresh (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d k : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (csl_indexed (indexed_after (fun x => x = nl) k)))))
      (run hdr ((h, allocs), (ctx, c))) .pure :=
  fun Hq Hf => rotate_agaf_core hdr nl k (indexed_after (fun x => x = nl) k)
    (fun _ hj => ⟨rfl, hj⟩) h allocs ctx c ns vs d .pure .pure Hq Hf

/-! ## Precondition controls -/

/-- Control 1: on the empty queue the first dereference is out of footprint, so the run is
stuck and satisfies no `AG` formula. -/
theorem empty_queue_no_ag (hdr : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) (vs : List Nat)
    (w : World (writerE (CSLObs Nat))) (φ : TiclL (writerE (CSLObs Nat))) :
    qrep hdr [] vs h → ¬ entails (AG φ) (run hdr ((h, allocs), (ctx, c))) w := by
  intro Hq H
  have H0 := qrep_null _ _ _ _ Hq
  have Hhd : h (hdr + 1) = some 0 := Hq.2.1
  have hbody : interp_state (sh (A := Nat)) (rot_body hdr) ((h, allocs), (ctx, c)) ~
      (CTree.stuck : ctreeW (CSLObs Nat) Bn ((PUnit ⊕ PUnit) × SSig)) :=
    sbisim_trans (interp_heapW_rd CSLObs.heap (h_sum csl_context_handler csl_emit_handler)
        (hdr + 1) h allocs (ctx, c) 0 _ Hhd)
      (interp_heapW_rd_missing CSLObs.heap (h_sum csl_context_handler csl_emit_handler)
        0 h allocs (ctx, c) _ H0)
  have hst : run hdr ((h, allocs), (ctx, c)) ~
      (CTree.stuck : ctreeW (CSLObs Nat) Bn (PUnit × SSig)) := by
    rw [run, rotate, interp_state_unfold_iter]
    refine sbisim_trans (sbisim_clo_bind_eq hbody fun _ => sbisim_refl _) ?_
    rw [stuck_bind]; exact sbisim_refl _
  exact ag_stuck ((proper_entails_meq _ hst).1 H)

/-- Every logged payload satisfies `Q` (Rocq `obs_sat`). -/
def obs_sat (Q : Nat → Prop) : World (writerE (CSLObs Nat)) → Prop :=
  fun w => ∀ o, w = .obs (E := writerE (CSLObs Nat)) (.emit o) ⟨⟩ → Q o.value

/-- Control 2, as an invariance: rotation permutes the queue, so every logged payload is a member
of the initial payload list. -/
theorem rotate_ag_obs (hdr : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) (ns vs : List Nat)
    (w : World (writerE (CSLObs Nat))) (Q : Nat → Prop) :
    (∀ x, x ∈ vs → Q x) → NotDone w → qrep hdr ns vs h → ns ≠ [] → obs_sat Q w →
    entails (AG (.now (obs_sat Q)))
      (interp_state (sh (A := Nat)) (rotate hdr) ((h, allocs), (ctx, c))) w := by
  intro HQ Hd Hq Hne Hw
  refine ag_state_iter (sh (A := Nat)) (k := fun _ : PUnit => rot_body hdr)
    (fun (_ : PUnit) (s : SSig) (w : World (writerE (CSLObs Nat))) =>
      (∃ ns' vs', qrep hdr ns' vs' s.1.1 ∧ ns' ≠ [] ∧ ∀ x, x ∈ vs' → Q x) ∧ obs_sat Q w)
    Hd ⟨⟨ns, vs, Hq, Hne, HQ⟩, Hw⟩ ?_
  rintro ⟨⟩ ⟨⟨h1, allocs1⟩, ctx1, c1⟩ w' Hd' ⟨⟨ns1, vs1, Hq1, Hne1, Hin1⟩, Hw'⟩
  obtain _ | ⟨a1, ns1'⟩ := ns1
  · exact (Hne1 rfl).elim
  obtain _ | ⟨v1, vs1'⟩ := vs1
  · simpa using qrep_len _ _ _ _ Hq1
  have Hv1 : Q v1 := Hin1 v1 (.head _)
  have Hheap : ∀ m : ManagedHeap, obs_sat Q (.obs (E := writerE (CSLObs Nat)) (.heap m) ⟨⟩) :=
    fun _ _ e => nomatch e
  refine ⟨⟨Hw', Hd'⟩, (proper_entails_meq _
    (rot_body_spec hdr a1 ns1' v1 vs1' h1 allocs1 ctx1 c1 Hq1)).2 ?_⟩
  simp only [queue_turn_logs, emit_list, List.foldr_cons, List.foldr_nil]
  refine an_log ?_ (ticll_top Hd')
  refine au_log ?_ ⟨fun o e => by cases e; exact Hv1, .obs _ _⟩
  refine au_log ?_ ⟨Hheap _, .obs _ _⟩
  refine au_log ?_ ⟨Hheap _, .obs _ _⟩
  refine au_log ?_ ⟨Hheap _, .obs _ _⟩
  refine .matchA (ret_ret (.obs _ _) ⟨⟨⟩, rfl, .obs _ _, ⟨ns1' ++ [a1], vs1' ++ [v1],
    (rot_heap_spec hdr a1 ns1' v1 vs1' h1 Hq1).1, by simp, ?_⟩, Hheap _⟩)
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact Hin1 x (.tail _ hx)
  · rw [List.mem_singleton.1 hx]; exact Hv1

/-- The control itself: an element outside the initial queue is never the payload of any
observation. -/
theorem absent_never_observed (hdr : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (nl : Nat) :
    qrep hdr ns vs h → ns ≠ [] → nl ∉ vs →
    entails (AG (.now (obs_sat fun x => x ≠ nl))) (run hdr ((h, allocs), (ctx, c))) .pure :=
  fun Hq Hne Hnin => rotate_ag_obs hdr h allocs ctx c ns vs .pure (fun x => x ≠ nl)
    (fun _ hx e => Hnin (e ▸ hx)) .pure Hq Hne (fun _ e => nomatch e)

end Examples.CSL.Queue.Recurrence
