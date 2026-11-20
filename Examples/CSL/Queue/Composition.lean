/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Shared

/-!
# Recurring per-queue progress for two active queues under any fair scheduler

Both workers of `parallel_queues` rotate their OWN queue in the shared heap; the scheduler is any
`FairScheduler`. The other queue is not a frame: it is rewritten on every one of its turns.
`step_focus`/`step_foreign` are the two resource-level turn lemmas; `step_foreign` is where active
composition differs from framing (the focused queue's representation survives a step of the OTHER
component, by `foreign_pres_rot`). The temporal layer is the fairness inversion rule
`agaf_fair_turns`: the invariant is both queues represented and disjoint, the rank is
(occurrence bound left, position of the element in the focused queue) under `lexnat`, and the
helpful slot is the focused worker. Everything is stated for an arbitrary focus, so the two
per-queue theorems are two instantiations of one proof
(← `examples/CSL/Queue/Composition.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Composition
open CTree Tisl Tisl.Notation Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Operations
open Examples.CSL.Queue.Separation Examples.CSL.Queue.Program Examples.CSL.Queue.Shared
open ITree (Effect)

section Composition
/- `fh` is the header of the queue whose progress we are proving, `gh` the other one. -/
variable (fh gh : Nat)

/-! ## The two resource-level turn lemmas -/

/-- A focused turn reuses `rot_heap_spec`, preserves the foreign queue through
`foreign_pres_rot`, and transports disjointness through `qcells_rot`. -/
theorem step_focus (nsf vsf nsg vsg : List Nat) (a pv : Nat) (h : Heap) :
    qrep fh (a :: nsf) (pv :: vsf) h → qrep gh nsg vsg h → Disj fh (a :: nsf) gh nsg →
    qrep fh (nsf ++ [a]) (vsf ++ [pv]) (rot_heap fh a (nsf.headD 0) (zof fh nsf) h) ∧
      qrep gh nsg vsg (rot_heap fh a (nsf.headD 0) (zof fh nsf) h) ∧
      Disj fh (nsf ++ [a]) gh nsg := fun hqf hqg hdj =>
  ⟨(rot_heap_spec fh a nsf pv vsf h hqf).1,
    foreign_pres_rot fh a nsf (pv :: vsf) gh nsg vsg h hqf hqg hdj,
    fun x hx => hdj x ((qcells_rot fh a nsf x).1 hx)⟩

/-- A turn of the FOREIGN queue: the focused queue's representation, at the same abstract queue,
survives a step of a component that is itself active. -/
theorem step_foreign (nsf vsf nsg vsg : List Nat) (b pw : Nat) (h : Heap) :
    qrep fh nsf vsf h → nsf ≠ [] → qrep gh (b :: nsg) (pw :: vsg) h →
    Disj fh nsf gh (b :: nsg) →
    qrep fh nsf vsf (rot_heap gh b (nsg.headD 0) (zof gh nsg) h) ∧
      qrep gh (nsg ++ [b]) (vsg ++ [pw]) (rot_heap gh b (nsg.headD 0) (zof gh nsg) h) ∧
      Disj fh nsf gh (nsg ++ [b]) := fun hqf _ hqg hdj =>
  ⟨foreign_pres_rot gh b nsg (pw :: vsg) fh nsf vsf h hqg hqf (Disj_sym _ _ _ _ hdj),
    (rot_heap_spec gh b nsg pw vsg h hqg).1,
    fun x hx hy => hdj x hx ((qcells_rot gh b nsg x).1 hy)⟩

/-! ## The invariant and rank -/

/-- BOTH queues are represented in the shared heap, their footprints are disjoint, and each still
contains its observed element. The ghost is the rank: (occurrence bound left, position of `nlf`
in the focused queue). -/
def Ifair (nlf nlg kb : Nat) (g : Nat × Nat) (s : SSig) : Prop :=
  ∃ nsf vsf nsg vsg dg,
    qrep fh nsf vsf (csl_memory s).1 ∧ qrep gh nsg vsg (csl_memory s).1 ∧
    Disj fh nsf gh nsg ∧
    find_index Nat.beq nlf vsf = some g.2 ∧ find_index Nat.beq nlg vsg = some dg ∧
    g.1 = kb - csl_counter s

/-- One turn of either slot: a focused turn hits the target or drops the rank; a foreign turn
drops the bound component or leaves the rank. -/
theorem worker_fair_turns (tagf tagg nlf nlg kb : Nat) (fi : Fin 2)
    (ps : Vector (CProg Unit) 2) (P : Indexed (Nat × Nat) → Prop) :
    ps[fi] = worker tagf fh → (∀ j : Fin 2, j ≠ fi → ps[j] = worker tagg gh) →
    (∀ j, kb ≤ j → P (stamp (tagf, nlf) j)) →
    FairTurns sh (csl_pool ps) fi (Ifair fh gh nlf nlg kb) (fun g => g) lexnat
      (csl_indexed P) := by
  intro hfi hother hP g s j hinv
  obtain ⟨nsf, vsf, nsg, vsg, dg, hqf, hqg, hdj, hff, hfg, hg⟩ := hinv
  obtain ⟨⟨h, allocs⟩, ctx, c⟩ := s
  obtain ⟨kc, d⟩ := g
  simp only [csl_memory, csl_counter] at hqf hqg hff hg
  subst hg
  rw [show (csl_pool ps)[j] = denote ps[j] by simp [csl_pool]]
  by_cases hj : j = fi
  · -- the FOCUSED queue's turn
    subst hj
    rw [hfi]
    match vsf, nsf, hqf, hff, hdj with
    | [], _, _, hff, _ => simp [find_index] at hff
    | _ :: _, [], hqf, _, _ => have := qrep_len _ _ _ _ hqf; simp at this
    | pv :: vsf', a :: nsf', hqf, hff, hdj =>
      obtain ⟨hqf', hqg', hdj'⟩ := step_focus fh gh nsf' vsf' nsg vsg a pv h hqf hqg hdj
      have hturn := exact_worker_turn tagf fh a nsf' pv vsf' h allocs ctx c hqf
      have hinv : ∀ d', find_index Nat.beq nlf (vsf' ++ [pv]) = some d' →
          Ifair fh gh nlf nlg kb (kb - (c + 1), d')
            ((rot_heap fh a (nsf'.headD 0) (zof fh nsf') h, allocs), (ctx, c + 1)) :=
        fun d' hd' => ⟨nsf' ++ [a], vsf' ++ [pv], nsg, vsg, dg, hqf', hqg', hdj', hd', hfg, rfl⟩
      -- the element is observed at the head, or the bound or its position falls
      obtain ⟨d', hd', ⟨rfl, hle⟩ | hrank⟩ :=
        find_index_rotation_progress Nat.beq (fun _ _ => Nat.beq_eq.to_iff) nlf pv vsf' d hff kb c
      · exact ⟨_, _, _, hturn, hinv d' hd', .inl ⟨_, .head _, hP c hle⟩⟩
      · exact ⟨_, _, _, hturn, hinv d' hd', .inr (.inl (Prod.lex_def.2 hrank))⟩
  · -- the FOREIGN queue's turn
    rw [hother j hj]
    have hnef : nsf ≠ [] := by
      rintro rfl
      cases vsf with
      | nil => simp [find_index] at hff
      | cons => have := qrep_len _ _ _ _ hqf; simp at this
    match vsg, nsg, hqg, hfg, hdj with
    | [], _, _, hfg, _ => simp [find_index] at hfg
    | _ :: _, [], hqg, _, _ => have := qrep_len _ _ _ _ hqg; simp at this
    | pw :: vsg', b :: nsg', hqg, hfg, hdj =>
      obtain ⟨hqf', hqg', hdj'⟩ := step_foreign fh gh nsf vsf nsg' vsg' b pw h hqf hnef hqg hdj
      obtain ⟨dg', hdg'⟩ := find_index_rotl_pres Nat.beq (fun _ _ => Nat.beq_eq.to_iff) _ _ _ _ hfg
      refine ⟨(kb - (c + 1), d), _, _,
        exact_worker_turn tagg gh b nsg' pw vsg' h allocs ctx c hqg,
        ⟨nsf, vsf, nsg' ++ [b], vsg' ++ [pw], dg', hqf', hqg', hdj', hff, hdg', rfl⟩, ?_⟩
      by_cases hle : kb ≤ c
      · exact .inr (.inr ⟨hj, by rw [show kb - (c + 1) = kb - c by omega]⟩)
      · exact .inr (.inl (.left _ _ (by omega)))

end Composition

/-! ## The two per-queue theorems

Both are instantiations of ONE proof: the focus is a parameter. After the fork of
`parallel_queues u v` the pool is `#v[worker 2 v, worker 1 u]`, so queue 1 lives in slot `1` and
queue 2 in slot `0`. The theorems hold from any focus and any policy state. -/

/-- Queue 1 (slot `1`, tag 1). -/
theorem fair_agaf_q1_gen (sch : Scheduler) [FairScheduler sch] (u v nl1 nl2 kb : Nat)
    (P : Indexed (Nat × Nat) → Prop) :
    (∀ j, kb ≤ j → P (stamp (1, nl1) j)) →
    ∀ (focus : Option (Fin 2)) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
      (ns1 vs1 ns2 vs2 : List Nat) (d1 d2 : Nat)
      (w : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))),
      qrep u ns1 vs1 h → qrep v ns2 vs2 h → Disj u ns1 v ns2 →
      find_index Nat.beq nl1 vs1 = some d1 → find_index Nat.beq nl2 vs2 = some d2 →
      NotDone w →
      entails (AG (AF (visWₜ (fair_obs (csl_indexed P)))))
        (run_fair_pool sch #v[worker 2 v, worker 1 u] focus st ((h, allocs), (ctx, c))) w := by
  intro HP focus st h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 w hq1 hq2 hdj hf1 hf2 hw
  have hother : ∀ j : Fin 2, j ≠ 1 → #v[worker 2 v, worker 1 u][j] = worker 2 v := by
    intro j hj
    match j, hj with
    | 0, _ => rfl
    | 1, hj => exact absurd rfl hj
  exact agaf_fair_turns sh sch _ 1 (Ifair u v nl1 nl2 kb) (fun g => g) lexnat (csl_indexed P)
    lexnat_wf (worker_fair_turns u v 1 2 nl1 nl2 kb 1 _ P rfl hother HP) (kb - c, d1) _ focus st w
    ⟨ns1, vs1, ns2, vs2, d2, hq1, hq2, hdj, hf1, hf2, rfl⟩ hw

/-- Queue 2 (slot `0`, tag 2). -/
theorem fair_agaf_q2_gen (sch : Scheduler) [FairScheduler sch] (u v nl1 nl2 kb : Nat)
    (P : Indexed (Nat × Nat) → Prop) :
    (∀ j, kb ≤ j → P (stamp (2, nl2) j)) →
    ∀ (focus : Option (Fin 2)) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
      (ns1 vs1 ns2 vs2 : List Nat) (d1 d2 : Nat)
      (w : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))),
      qrep u ns1 vs1 h → qrep v ns2 vs2 h → Disj u ns1 v ns2 →
      find_index Nat.beq nl1 vs1 = some d1 → find_index Nat.beq nl2 vs2 = some d2 →
      NotDone w →
      entails (AG (AF (visWₜ (fair_obs (csl_indexed P)))))
        (run_fair_pool sch #v[worker 2 v, worker 1 u] focus st ((h, allocs), (ctx, c))) w := by
  intro HP focus st h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 w hq1 hq2 hdj hf1 hf2 hw
  have hother : ∀ j : Fin 2, j ≠ 0 → #v[worker 2 v, worker 1 u][j] = worker 1 u := by
    intro j hj
    match j, hj with
    | 0, hj => exact absurd rfl hj
    | 1, _ => rfl
  exact agaf_fair_turns sh sch _ 0 (Ifair v u nl2 nl1 kb) (fun g => g) lexnat (csl_indexed P)
    lexnat_wf (worker_fair_turns v u 2 1 nl2 nl1 kb 0 _ P rfl hother HP) (kb - c, d2) _ focus st w
    ⟨ns2, vs2, ns1, vs1, d1, hq2, hq1, Disj_sym _ _ _ _ hdj, hf2, hf1, rfl⟩ hw

end Examples.CSL.Queue.Composition
