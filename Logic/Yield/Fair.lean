/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Execution
public import Logic.Yield.SBisimAlign
public import Logic.CTree.AF
public import Logic.CTree.TraceRules

/-!
# Scheduler-generic fairness for yielding pools

The direct policy scheduler logs one selected-slot observation per turn; user logs are relabelled
into the program side of `W ⊕ Nat`. Fairness is a property of the policy's own pick stream
(`sched_trace`), conditional on reaching cooperative scheduling boundaries; round robin is fair,
nondeterministic selection is not (← `CTree/Interp/Yield/Fair.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction Tisl.Notation
open ITree (Effect)

/-- Raw handler equations remain valid after relabelling. -/
theorem relabel_equ_sb {W X : Type} (t u : ctreeW W Bn X) (h : t = u) :
    translate relabel_log t ~ translate relabel_log u :=
  h ▸ sbisim_refl _

/-! ## Policy traces and fairness -/

/-- The policy's own pick stream for a live pool of size `n+1`. -/
def sched_trace (sch : Scheduler) (n : Nat) (st : sch.sched_state) : ctreeW Nat Bn PUnit :=
  br_alts (sch.sched_arity n st) fun a =>
    .vis (E := writerE Nat) (slot_index (sch.sched_pick n st a).1) fun _ =>
      sched_trace sch n (sch.sched_pick n st a).2
partial_fixpoint

theorem unfold_sched_trace (sch : Scheduler) (n : Nat) (st : sch.sched_state) :
    sched_trace sch n st =
      br_alts (sch.sched_arity n st) fun a =>
        .vis (E := writerE Nat) (slot_index (sch.sched_pick n st a).1) fun _ =>
          sched_trace sch n (sch.sched_pick n st a).2 := by
  rw [sched_trace]

theorem sched_trace_select (sch : Scheduler) (n : Nat) (st : sch.sched_state) :
    sched_trace sch n st ~
      CTree.brn (sch.sched_arity n st + 1) fun a =>
        .vis (E := writerE Nat) (slot_index (sch.sched_pick n st a).1) fun _ =>
          sched_trace sch n (sch.sched_pick n st a).2 := by
  rw [unfold_sched_trace]
  have key : ∀ m (k : Fin (m + 1) → ctreeW Nat Bn PUnit), br_alts m k ~ CTree.brn (m + 1) k
    | 0, k => sbisim_symm (sb_br_l _ (⟨0⟩ : ULift (Fin 1)) _ _ fun _ =>
        have h : ∀ y : Fin 1, k y ~ k 0 := fun y => by rw [fin1_eq y]; exact sbisim_refl _
        h _)
    | _ + 1, _ => sbisim_refl _
  exact key _ _

/-- Exact residuals matter for transition induction: the uniform selection bisimulation is not a
replacement for these native trace transitions. -/
theorem sched_trace_pick (sch : Scheduler) (n : Nat) (st : sch.sched_state)
    (a : Fin (sch.sched_arity n st + 1)) (w : World (writerE Nat)) (hw : NotDone w) :
    ktrans (sched_trace sch n st) w (sched_trace sch n (sch.sched_pick n st a).2)
      (.obs (E := writerE Nat) (slot_index (sch.sched_pick n st a).1) ⟨⟩) := by
  rw [unfold_sched_trace]
  exact ktrans_br_alts.2 ⟨a, ktrans_vis.2 ⟨⟨⟩, rfl, rfl, hw⟩⟩

theorem sched_trace_pick_inv (sch : Scheduler) (n : Nat) (st : sch.sched_state)
    (w : World (writerE Nat)) (t' : ctreeW Nat Bn PUnit) (w' : World (writerE Nat))
    (tr : ktrans (sched_trace sch n st) w t' w') :
    ∃ a, w' = .obs (E := writerE Nat) (slot_index (sch.sched_pick n st a).1) ⟨⟩ ∧
      sched_trace sch n (sch.sched_pick n st a).2 = t' := by
  rw [unfold_sched_trace] at tr
  obtain ⟨a, tr⟩ := ktrans_br_alts.1 tr
  obtain ⟨⟨⟩, rfl, h, -⟩ := ktrans_vis.1 tr
  exact ⟨a, rfl, h⟩

/-- Fairness: from every policy state, every slot of a fixed-size pool is picked again and
again. -/
class FairScheduler (sch : Scheduler) : Prop where
  fair_scheduled : ∀ n (i : Fin (n + 1)) (st : sch.sched_state) (w : World (writerE Nat)),
    NotDone w → entails (AG (AF (visWₜ (slot_index i = ·)))) (sched_trace sch n st) w

export FairScheduler (fair_scheduled)

/-- Induction-friendly witness: along every alternative that avoids slot `i`, slot `i` is still
picked after finitely many scheduling points. -/
inductive EventuallyPicks (sch : Scheduler) (n : Nat) (i : Fin (n + 1)) : sch.sched_state → Prop
  | intro (st : sch.sched_state) :
      (∀ a, (sch.sched_pick n st a).1 ≠ i → EventuallyPicks sch n i (sch.sched_pick n st a).2) →
      EventuallyPicks sch n i st

/-- A destination policy may duplicate a source scheduling point only while strictly decreasing
its own well-founded rank. Every offered destination choice must match a source choice,
including its selected slot. -/
theorem eventually_picks_simulation {V : Type} (source target : Scheduler) (n : Nat)
    (i : Fin (n + 1)) (Rel : target.sched_state → source.sched_state → Prop)
    (rank : target.sched_state → V) (ltV : V → V → Prop) (hwf : WellFounded ltV)
    (hsim : ∀ dst src offer, Rel dst src → ∃ offer',
      (target.sched_pick n dst offer).1 = (source.sched_pick n src offer').1 ∧
      (Rel (target.sched_pick n dst offer).2 (source.sched_pick n src offer').2 ∨
       (Rel (target.sched_pick n dst offer).2 src ∧
        ltV (rank (target.sched_pick n dst offer).2) (rank dst)))) :
    ∀ src dst, EventuallyPicks source n i src → Rel dst src → EventuallyPicks target n i dst := by
  intro src dst hep
  induction hep generalizing dst with
  | intro src _ ih =>
    refine (InvImage.wf rank hwf).induction (C := fun dst => Rel dst src →
      EventuallyPicks target n i dst) dst fun dst ihrank hrel => .intro dst fun offer hmiss => ?_
    obtain ⟨offer', hpick, hadv | ⟨hstay, hlt⟩⟩ := hsim dst src offer hrel
    · exact ih offer' (hpick ▸ hmiss) _ hadv
    · exact ihrank _ hlt hstay

section FairBridge
variable (sch : Scheduler) (n : Nat) (i : Fin (n + 1))

theorem eventually_picks_af (st : sch.sched_state) (w : World (writerE Nat))
    (hep : EventuallyPicks sch n i st) (hw : NotDone w) :
    entails (AF (visWₜ (slot_index i = ·))) (sched_trace sch n st) w := by
  induction hep generalizing w with
  | intro st _ ih =>
    rw [unfold_sched_trace]
    refine au_br_alts (ticll_top hw) ⟨0, (can_step_vis PUnit.unit).2 hw⟩ fun a t' w' tr => ?_
    obtain ⟨⟨⟩, rfl, rfl, -⟩ := ktrans_vis.1 tr
    by_cases hpick : (sch.sched_pick n st a).1 = i
    · exact .matchA ⟨.obs _ _ (hpick ▸ rfl), .obs _ _⟩
    · exact ih a hpick _ (.obs _ _)

theorem af_trace_eventually_picks (t : ctreeW Nat Bn PUnit) (w : World (writerE Nat))
    (h : entails (AF (visWₜ (slot_index i = ·))) t w) :
    ∀ st, t = sched_trace sch n st → w ≠ .obs (E := writerE Nat) (slot_index i) ⟨⟩ →
      EventuallyPicks sch n i st := by
  induction h with
  | matchA hq =>
    intro st _ hw
    obtain ⟨hv, -⟩ := hq
    cases hv with
    | obs e v h => cases h; exact (hw rfl).elim
  | stepA hp _ _ ih =>
    intro st et _
    exact .intro st fun a hne => ih _ _ (by rw [et]; exact sched_trace_pick sch n st a _ hp.2)
      _ rfl fun ew => hne (Fin.ext (World.obs.inj ew).1)

theorem fair_eventually_picks [FairScheduler sch] (st : sch.sched_state) :
    EventuallyPicks sch n i st :=
  af_trace_eventually_picks sch n i _ .pure (agc_unfold.1 (fair_scheduled n i st .pure .pure)).1
    st rfl nofun

end FairBridge

/-- Any policy whose picks are inductively fair is a `FairScheduler`. -/
theorem eventually_picks_fair (sch : Scheduler)
    (hep : ∀ n (i : Fin (n + 1)) st, EventuallyPicks sch n i st) : FairScheduler sch := by
  refine ⟨fun n i st w hw => ?_⟩
  refine coinduction (b := agcF (entails (AF (visWₜ (slot_index i = ·)))))
    (fun p : (Σ' (st : sch.sched_state) (w : World (writerE Nat)), NotDone w) =>
      sched_trace sch n p.1) (fun p => p.2.1) ?_ ⟨st, w, hw⟩
  rintro R - cih ⟨st, w, hw⟩
  refine ⟨eventually_picks_af sch n i st w (hep n i st) hw, ?_, fun t' w' tr => ?_⟩
  · rw [unfold_sched_trace]
    exact can_step_br_alts.2 ⟨0, (can_step_vis PUnit.unit).2 hw⟩
  · obtain ⟨a, rfl, rfl⟩ := sched_trace_pick_inv sch n st w t' w' tr
    exact cih ⟨_, _, .obs _ _⟩

theorem rr_eventually_picks (n : Nat) (i : Fin (n + 1)) :
    ∀ m : Nat, EventuallyPicks rr_scheduler n i m := by
  have hk : ∀ k (m : Nat), (m + k) % (n + 1) = slot_index i →
      EventuallyPicks rr_scheduler n i m := by
    intro k
    induction k with
    | zero =>
      intro m hm
      refine @EventuallyPicks.intro rr_scheduler n i m fun a hne => (hne (Fin.ext ?_)).elim
      exact hm
    | succ k ih =>
      intro m hm
      exact @EventuallyPicks.intro rr_scheduler n i m fun _ _ =>
        ih (m + 1) (by rw [← hm]; congr 1; omega)
  intro m
  refine hk (n + 1 - m % (n + 1) + slot_index i) m ?_
  have hdm := Nat.div_add_mod m (n + 1)
  have hub := Nat.mod_lt m (show n + 1 > 0 by omega)
  have hi := i.isLt
  have : m + (n + 1 - m % (n + 1) + slot_index i) =
      slot_index i + (n + 1) * (m / (n + 1) + 1) := by
    rw [Nat.mul_succ]
    generalize (n + 1) * (m / (n + 1)) = q at hdm ⊢
    simp only [slot_index]
    omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

instance rr_fair : FairScheduler rr_scheduler :=
  eventually_picks_fair rr_scheduler fun n i => rr_eventually_picks n i

/-! ## Nondeterministic selection is not fair

With two or more slots, the alternative that picks another slot leads back to the same stateless
scheduling point, so no finite witness that slot `i` is eventually picked exists. -/

theorem nd_not_eventually_picks (n : Nat) (i : Fin (n + 2)) (st : nd_scheduler.sched_state) :
    ¬ EventuallyPicks nd_scheduler (n + 1) i st := by
  intro hep
  induction hep with
  | intro st _ ih =>
    by_cases hi : i.val = 0
    · exact ih ⟨1, show 1 < n + 2 by omega⟩ fun h => by
        have := congrArg Fin.val h
        change 1 = i.val at this
        omega
    · exact ih ⟨0, show 0 < n + 2 by omega⟩ fun h => hi (congrArg Fin.val h).symm

/-- Hence no `FairScheduler nd_scheduler` instance exists: fairness would yield the inductive
witness for slot `0` of a two-slot pool. -/
theorem nd_not_fair : ¬ FairScheduler nd_scheduler := fun _ =>
  nd_not_eventually_picks 0 0 ⟨⟩ (fair_eventually_picks nd_scheduler 1 0 ⟨⟩)

/-! ## Inversion rules: invariant, well-founded rank, helpful slot

The certificate is the Manna–Pnueli response rule under justice: a turn either reaches the goal,
or strictly decreases the rank, or is taken by a non-helpful slot and changes neither rank nor
helpful slot. Fairness of the policy guarantees that the helpful slot is eventually picked. The
pool text is part of the invariant: threads may change code at turn boundaries. -/

section PoolRulesFair
variable {E : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))
  (sch : Scheduler) {n : Nat}

structure FairCertificate {G V : Type} (Inv : G → Pool E Bn (n + 1) → Sg → Prop)
    (rank : G → V) (ltV : V → V → Prop) (target : G → Fin (n + 1)) (P : W → Prop) : Prop where
  fair_wf : WellFounded ltV
  fair_turn : ∀ g ts σ (j : Fin (n + 1)), Inv g ts σ →
    ∃ g' logs residual σ',
      ThreadSegment handler (fun _ t u => t = u) ts[j] σ logs residual σ' ∧
      Inv g' (ts.set j residual) σ' ∧
      ((∃ o ∈ logs, P o) ∨ ltV (rank g') (rank g) ∨
        (j ≠ target g ∧ rank g' = rank g ∧ target g' = target g))

/-- Closed turns alone, for the `AG` half. -/
def ClosedPool {G : Type} (Inv : G → Pool E Bn (n + 1) → Sg → Prop) : Prop :=
  ∀ g ts σ (j : Fin (n + 1)), Inv g ts σ →
    ∃ g' logs residual σ',
      ThreadSegment handler (fun _ t u => t = u) ts[j] σ logs residual σ' ∧
      Inv g' (ts.set j residual) σ'

theorem fair_certificate_closed {G V : Type} (Inv : G → Pool E Bn (n + 1) → Sg → Prop)
    (rank : G → V) (ltV : V → V → Prop) (target : G → Fin (n + 1)) (P : W → Prop)
    (hc : FairCertificate handler Inv rank ltV target P) : ClosedPool handler Inv :=
  fun g ts σ j hinv =>
    let ⟨g', logs, residual, σ', hseg, hinv', _⟩ := hc.fair_turn g ts σ j hinv
    ⟨g', logs, residual, σ', hseg, hinv'⟩

/-- A focused turn of slot `j` is its relabelled logs followed by the unfocused pool. -/
private theorem segment_fair (ts : Pool E Bn (n + 1)) (j : Fin (n + 1)) (st : sch.sched_state)
    (σ : Sg) (logs : List W) (residual : Thread E Bn) (σ' : Sg)
    (hseg : ThreadSegment handler (fun _ t u => t = u) ts[j] σ logs residual σ') :
    interp_schedule_fair sch handler (n + 1) ts (some j) st σ ~
      emit_list (logs.map .inl)
        (interp_schedule_fair sch handler (n + 1) (ts.set j residual) none st σ') :=
  segment_interp_fair sch handler _ (fun _ t u h => relabel_equ_sb t u h) n ts j st σ logs
    residual σ' hseg

/-- The `AG` half: closed turns keep `φ` invariant on the fair runner. -/
theorem ag_pool_fair_invariance {G : Type} (Inv : G → Pool E Bn (n + 1) → Sg → Prop)
    (φ : TiclL (writerE (W ⊕ Nat))) (hclosed : ClosedPool handler Inv)
    (hlog : ∀ (o : W) (t : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) w, NotDone w →
      entails φ t (.obs (E := writerE (W ⊕ Nat)) (.inl o) ⟨⟩) →
      entails φ (CTree.vis (E := writerE (W ⊕ Nat)) (.inl o) fun _ => t) w)
    (hφ : ∀ g ts σ st w, Inv g ts σ → NotDone w →
      entails φ (interp_schedule_fair sch handler (n + 1) ts none st σ) w) :
    ∀ g ts σ focus st w, Inv g ts σ → NotDone w →
      entails (AG φ) (interp_schedule_fair sch handler (n + 1) ts focus st σ) w := by
  have hpref : ∀ (xs : List W) (t : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)),
      (∀ w, NotDone w → entails φ t w) →
        ∀ w, NotDone w → entails φ (emit_list (xs.map .inl) t) w := by
    intro xs t ht
    induction xs with
    | nil => exact ht
    | cons o xs ih =>
      intro w hw
      rw [List.map_cons, emit_list_cons]
      exact hlog o _ w hw (ih _ (.obs _ _))
  have hcoind := coinduction (b := agcF (entails φ))
    (ι := {p : ctreeW (W ⊕ Nat) Bn (PUnit × Sg) × World (writerE (W ⊕ Nat)) //
      NotDone p.2 ∧ ∃ (g : G) (ts : Pool E Bn (n + 1)) (σ : Sg) (st : sch.sched_state)
        (xs : List W), Inv g ts σ ∧
        p.1 ~ emit_list (xs.map .inl) (interp_schedule_fair sch handler (n + 1) ts none st σ)})
    (fun p => p.1.1) (fun p => p.1.2) ?_
  · intro g ts σ focus st w hinv hw
    cases focus with
    | none => exact hcoind ⟨(_, w), hw, g, ts, σ, st, [], hinv, sbisim_refl _⟩
    | some j =>
      obtain ⟨g', logs, residual, σ', hseg, hinv'⟩ := hclosed g ts σ j hinv
      exact hcoind ⟨(_, w), hw, g', _, σ', st, logs, hinv',
        segment_fair handler sch ts j st σ logs residual σ' hseg⟩
  rintro R - cih ⟨⟨t, w⟩, hw, g, ts, σ, st, xs, hinv, ht⟩
  refine ⟨(proper_entails_meq φ ht).2 (hpref xs _ (fun w hw => hφ g ts σ st w hinv hw) w hw), ?_⟩
  cases xs with
  | cons o rest =>
    rw [List.map_cons, emit_list_cons] at ht
    refine ⟨(proper_can_step ht).2 ((can_step_vis PUnit.unit).2 hw), fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht tr
    obtain ⟨⟨⟩, rfl, rfl, -⟩ := ktrans_vis.1 tr
    exact cih ⟨(t', _), .obs _ _, g, ts, σ, st, rest, hinv, hu⟩
  | nil =>
    have ht' := sbisim_trans ht (interp_schedule_fair_select sch handler n ts st σ)
    refine ⟨(proper_can_step ht').2
      (can_step_br_alts.2 ⟨0, (can_step_vis PUnit.unit).2 hw⟩),
      fun t' w' tr => ?_⟩
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht' tr
    obtain ⟨a, tr⟩ := ktrans_br_alts.1 tr
    obtain ⟨⟨⟩, rfl, rfl, -⟩ := ktrans_vis.1 tr
    obtain ⟨g', logs, residual, σ', hseg, hinv'⟩ := hclosed g ts σ _ hinv
    exact cih ⟨(t', _), .obs _ _, g', _, σ', _, logs, hinv',
      sbisim_trans hu (segment_fair handler sch ts _ _ σ logs residual σ' hseg)⟩

/-- The `AF` half: the helpful slot is eventually picked, and every turn makes progress toward
the goal or leaves the rank alone. -/
theorem aul_pool_fair_eventually [FairScheduler sch] {G V : Type}
    (Inv : G → Pool E Bn (n + 1) → Sg → Prop) (rank : G → V) (ltV : V → V → Prop)
    (target : G → Fin (n + 1)) (P : W → Prop)
    (hcert : FairCertificate handler Inv rank ltV target P) :
    ∀ g ts σ focus st w, Inv g ts σ → NotDone w →
      entails (AF (visWₜ (fair_obs P)))
        (interp_schedule_fair sch handler (n + 1) ts focus st σ) w := by
  intro g
  refine (InvImage.wf rank hcert.fair_wf).induction (C := fun g => ∀ ts σ focus st w,
    Inv g ts σ → NotDone w → entails (AF (visWₜ (fair_obs P)))
      (interp_schedule_fair sch handler (n + 1) ts focus st σ) w) g fun g ihrank => ?_
  -- A hit inside the logs of a turn.
  have hhit : ∀ (logs : List W) (t : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) w, NotDone w →
      (∃ o ∈ logs, P o) → entails (AF (visWₜ (fair_obs P))) (emit_list (logs.map .inl) t) w :=
    fun logs _ w hw ⟨o, hin, hp⟩ =>
      af_emit_list_member _ _ w _ (.inl o) hw (List.mem_map_of_mem hin) hp
  -- A strict rank drop.
  have hdrop : ∀ g' ts σ st (logs : List W) w, Inv g' ts σ → ltV (rank g') (rank g) →
      NotDone w → entails (AF (visWₜ (fair_obs P))) (emit_list (logs.map .inl)
        (interp_schedule_fair sch handler (n + 1) ts none st σ)) w :=
    fun g' ts σ st logs w hinv hlt hw =>
      af_emit_list _ _ w _ hw (ihrank g' hlt ts σ none st _ hinv (after_logs_not_done _ hw))
  -- A turn of the helpful slot: a hit or a strict rank drop.
  have htarget : ∀ g0 ts σ st w, Inv g0 ts σ → rank g0 = rank g → target g0 = target g →
      NotDone w → entails (AF (visWₜ (fair_obs P)))
        (interp_schedule_fair sch handler (n + 1) ts (some (target g)) st σ) w := by
    intro g0 ts σ st w hinv hr htg hw
    obtain ⟨g', logs, residual, σ', hseg, hinv', hcase⟩ := hcert.fair_turn g0 ts σ (target g) hinv
    refine (proper_entails_meq _ (segment_fair handler sch ts _ st σ logs residual σ' hseg)).2 ?_
    rcases hcase with hp | hlt | ⟨hne, -⟩
    · exact hhit logs _ w hw hp
    · exact hdrop g' _ σ' st logs w hinv' (hr ▸ hlt) hw
    · exact (hne htg.symm).elim
  -- Until the helpful slot is picked, the rank is preserved.
  have hinner : ∀ st, EventuallyPicks sch n (target g) st → ∀ g0 ts σ focus w,
      Inv g0 ts σ → rank g0 = rank g → target g0 = target g → NotDone w →
      entails (AF (visWₜ (fair_obs P)))
        (interp_schedule_fair sch handler (n + 1) ts focus st σ) w := by
    intro st hep
    induction hep with
    | intro st0 _ ih =>
      have hnone : ∀ g0 ts σ w, Inv g0 ts σ → rank g0 = rank g → target g0 = target g →
          NotDone w → entails (AF (visWₜ (fair_obs P)))
            (interp_schedule_fair sch handler (n + 1) ts none st0 σ) w := by
        intro g0 ts σ w hinv hr htg hw
        refine (proper_entails_meq _ (interp_schedule_fair_select sch handler n ts st0 σ)).2 ?_
        refine au_br_alts (ticll_top hw) ⟨0, (can_step_vis PUnit.unit).2 hw⟩
          fun a t' w' tr => ?_
        obtain ⟨⟨⟩, rfl, rfl, -⟩ := ktrans_vis.1 tr
        by_cases hj : (sch.sched_pick n st0 a).1 = target g
        · rw [hj]; exact htarget g0 ts σ _ _ hinv hr htg (.obs _ _)
        · exact ih a hj g0 ts σ _ _ hinv hr htg (.obs _ _)
      intro g0 ts σ focus w hinv hr htg hw
      cases focus with
      | none => exact hnone g0 ts σ w hinv hr htg hw
      | some j =>
        obtain ⟨g', logs, residual, σ', hseg, hinv', hcase⟩ := hcert.fair_turn g0 ts σ j hinv
        refine (proper_entails_meq _ (segment_fair handler sch ts _ st0 σ logs residual σ'
          hseg)).2 ?_
        rcases hcase with hp | hlt | ⟨-, hr', htg'⟩
        · exact hhit logs _ w hw hp
        · exact hdrop g' _ σ' st0 logs w hinv' (hr ▸ hlt) hw
        · exact af_emit_list _ _ w _ hw (hnone g' _ σ' _ hinv' (hr'.trans hr) (htg'.trans htg)
            (after_logs_not_done _ hw))
  intro ts σ focus st w hinv hw
  exact hinner st (fair_eventually_picks sch n (target g) st) g ts σ focus w hinv rfl rfl hw

/-- The fairness inversion rule: witnesses are an invariant, a well-founded rank and a helpful
slot. -/
theorem agaf_pool_fair [FairScheduler sch] {G V : Type}
    (Inv : G → Pool E Bn (n + 1) → Sg → Prop) (rank : G → V) (ltV : V → V → Prop)
    (target : G → Fin (n + 1)) (P : W → Prop)
    (hcert : FairCertificate handler Inv rank ltV target P) :
    ∀ g ts σ focus st w, Inv g ts σ → NotDone w →
      entails (AG (AF (visWₜ (fair_obs P))))
        (interp_schedule_fair sch handler (n + 1) ts focus st σ) w :=
  ag_pool_fair_invariance handler sch Inv _
    (fair_certificate_closed handler Inv rank ltV target P hcert)
    (fun _ _ _ hw ht => (au_vis PUnit.unit).1 (.inr ⟨ticll_top hw, fun _ => ht⟩))
    (fun g ts σ st w hinv hw =>
      aul_pool_fair_eventually handler sch Inv rank ltV target P hcert g ts σ none st w hinv hw)

/-- Fixed pool text, finite log lists, constant helpful slot. -/
def FairTurns {G V : Type} (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (Inv : G → Sg → Prop)
    (rank : G → V) (ltV : V → V → Prop) (P : W → Prop) : Prop :=
  ∀ g σ (j : Fin (n + 1)), Inv g σ →
    ∃ g' σ' logs,
      segment_to handler (fun _ t u => t = u) ts[j] σ logs ts[j] σ' ∧ Inv g' σ' ∧
      ((∃ o ∈ logs, P o) ∨ ltV (rank g') (rank g) ∨ (j ≠ i ∧ rank g' = rank g))

theorem fair_turns_certificate {G V : Type} (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (Inv : G → Sg → Prop) (rank : G → V) (ltV : V → V → Prop) (P : W → Prop)
    (hwf : WellFounded ltV) (hturns : FairTurns handler ts i Inv rank ltV P) :
    FairCertificate handler (fun g ts' σ => Inv g σ ∧ pool_guard_equ ts' ts) rank ltV
      (fun _ => i) P := by
  refine ⟨hwf, fun g0 ts' σ j ⟨hinv0, hpool⟩ => ?_⟩
  obtain ⟨g', σ', logs, ⟨residual, hseg, htail⟩, hinv', hcase⟩ := hturns g0 σ j hinv0
  refine ⟨g', logs, residual, σ',
    (guard_equ_segment_iff handler _ ts'[j] ts[j] (hpool j) σ logs residual σ').2 hseg,
    ⟨hinv', ?_⟩, ?_⟩
  · have := vector_replace_pointwise (fun a b : Thread E Bn => guard_equ a b) ts' ts j residual
      ts[j] (fun k _ => hpool k) htail
    exact fun k => by simpa using this k
  · rcases hcase with hp | hlt | ⟨hne, hr⟩
    · exact .inl hp
    · exact .inr (.inl hlt)
    · exact .inr (.inr ⟨hne, hr, rfl⟩)

theorem agaf_fair_turns [FairScheduler sch] {G V : Type} (ts : Pool E Bn (n + 1))
    (i : Fin (n + 1)) (Inv : G → Sg → Prop) (rank : G → V) (ltV : V → V → Prop) (P : W → Prop)
    (hwf : WellFounded ltV) (hturns : FairTurns handler ts i Inv rank ltV P) :
    ∀ g σ focus st w, Inv g σ → NotDone w →
      entails (AG (AF (visWₜ (fair_obs P))))
        (interp_schedule_fair sch handler (n + 1) ts focus st σ) w :=
  fun g σ focus st w hinv hw =>
    agaf_pool_fair handler sch (fun g ts' σ => Inv g σ ∧ pool_guard_equ ts' ts) rank ltV
      (fun _ => i) P (fair_turns_certificate handler ts i Inv rank ltV P hwf hturns)
      g ts σ focus st w ⟨hinv, fun _ => guard_equ_equ _ _ rfl⟩ hw

/-- Abstract-model clients: ghost data projects to model states. -/
theorem agaf_pool_simulation_fair [FairScheduler sch] {St Act G V : Type}
    (actor : Fin (n + 1) → Act) (slot : Act → Fin (n + 1)) (slot_actor : ∀ i, slot (actor i) = i)
    (step : Act → St → Option (St × List W)) (pool_of : St → Pool E Bn (n + 1))
    (agree : Sg → St → Prop) (Inv : St → Prop)
    (Hsim : PoolSimulation n handler slot step pool_of agree Inv)
    (st_of : G → St) (InvG : G → Prop) (rank : G → V) (ltV : V → V → Prop)
    (target : G → Fin (n + 1)) (P : W → Prop) (hwf : WellFounded ltV)
    (hInv : ∀ g, InvG g → Inv (st_of g))
    (hturn : ∀ g who s' event, InvG g → step who (st_of g) = some (s', event) →
      ∃ g', st_of g' = s' ∧ InvG g' ∧
        ((∃ o ∈ event, P o) ∨ ltV (rank g') (rank g) ∨
          (slot who ≠ target g ∧ rank g' = rank g ∧ target g' = target g))) :
    ∀ g ts σ focus st w, InvG g → agree σ (st_of g) → pool_guard_equ ts (pool_of (st_of g)) →
      NotDone w →
      entails (AG (AF (visWₜ (fair_obs P))))
        (interp_schedule_fair sch handler (n + 1) ts focus st σ) w := by
  intro g ts σ focus st w hg hagree hpool hw
  refine agaf_pool_fair handler sch
    (fun g ts σ => InvG g ∧ agree σ (st_of g) ∧ pool_guard_equ ts (pool_of (st_of g)))
    rank ltV target P ⟨hwf, ?_⟩ g ts σ focus st w ⟨hg, hagree, hpool⟩ hw
  rintro g0 ts0 σ j ⟨hg0, hagree0, hpool0⟩
  obtain ⟨s', event, hstep, -⟩ := Hsim.simulation_total (actor j) (st_of g0) (hInv g0 hg0)
  obtain ⟨g', rfl, hg', hcase⟩ := hturn g0 (actor j) s' event hg0 hstep
  obtain ⟨residual, σ', hseg, hagree', hpool'⟩ := selected_turn_segment Hsim ts0 (st_of g0)
    (actor j) (st_of g') event σ (hInv g0 hg0) hagree0 hpool0 hstep
  simp only [slot_actor] at hseg hpool' hcase
  exact ⟨g', event, residual, σ', hseg, ⟨hg', hagree', hpool'⟩, hcase⟩

end PoolRulesFair

-- Not ported: `exactW` and the local `fair` (Rocq `Abbreviation`s: written out as
-- `fun _ t u => t = u` and `interp_schedule_fair sch handler (n + 1)`).

end Tisl.Yield
