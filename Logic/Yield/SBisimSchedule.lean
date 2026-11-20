/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.SBisim

/-!
# Scheduler congruence for strong bisimulation

Transition lifting from the focused thread to the scheduler, and the main congruence
`sbisim_schedule_policy`: the same policy, focus and state over pointwise bisimilar
**branch-free** pools give bisimilar scheduled trees; ND and RR specializations
(← `CTree/Interp/Yield/SBisim.v`, lines 331-1096).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Lean.Order Coinduction
open ITree (Effect)

section SchedulerTransitions
variable {E B : Effect.{0}} [Bn -< B] (sch : Scheduler)

theorem schedule_policy_some_pool_equ {m : Nat} (v w : Pool E B (m + 1)) (i : Fin (m + 1))
    (st : sch.sched_state) (h : pool_equ v w) :
    schedule_policy sch (m + 1) v (some i) st = schedule_policy sch (m + 1) w (some i) st :=
  schedule_policy_pool_proper sch _ v w _ st h

omit [Bn -< B] in
theorem pool_equ_refl {n : Nat} (v : Pool E B n) : pool_equ v v := fun _ => rfl

omit [Bn -< B] in
theorem replace_pool_idem_equ {n : Nat} (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (a b : Thread E B) : pool_equ (v.set i b) ((v.set i a).set i b) := by
  rw [Vector.set_set]; exact pool_equ_refl _

omit [Bn -< B] in
theorem remove_pool_agree {n : Nat} (v w : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : ∀ j, i ≠ j → v[j] = w[j]) : pool_equ (v.eraseIdx i) (w.eraseIdx i) :=
  vector_remove_pointwise (fun a b : Thread E B => a = b) v w i h

omit [Bn -< B] in
theorem remove_replace_pool_equ {n : Nat} (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (a : Thread E B) : pool_equ ((v.set i a).eraseIdx i) (v.eraseIdx i) :=
  (show (v.set i a).eraseIdx i = v.eraseIdx i from vector_remove_replace v i a) ▸ pool_equ_refl _

/-- Every unfocused alternative is a transition logging the selected slot (needs a lawful
`Bn` embedding to reach every alternative of the hidden branch). -/
theorem trans_schedule_policy_no_focus_nonempty [LawfulSubeffect Bn B] (n : Nat)
    (v : Pool E B (n + 1)) (st : sch.sched_state) (a : Fin (sch.sched_arity n st + 1)) :
    trans (.obs (E := E ⊕ₑ schedE) (.inr (slot_index (sch.sched_pick n st a).1)) ⟨⟩)
      (schedule_policy sch (n + 1) v none st)
      (schedule_policy sch (n + 1) v (some (sch.sched_pick n st a).1)
        (sch.sched_pick n st a).2) := by
  rw [schedule_policy_no_focus_equ]
  exact trans_br_alts _ a (trans_vis _ _)

theorem trans_schedule_policy_no_focus_inv (n : Nat) (v : Pool E B (n + 1))
    (st : sch.sched_state) (l : Label (E ⊕ₑ schedE)) (q : Completed E B)
    (h : trans l (schedule_policy sch (n + 1) v none st) q) :
    ∃ a, l = .obs (.inr (slot_index (sch.sched_pick n st a).1)) ⟨⟩ ∧
      q = schedule_policy sch (n + 1) v (some (sch.sched_pick n st a).1)
        (sch.sched_pick n st a).2 := by
  rw [schedule_policy_no_focus_equ] at h
  obtain ⟨a, h⟩ := trans_br_alts_inv _ h
  obtain ⟨⟨⟩, rfl, rfl⟩ := trans_vis_inv h
  exact ⟨a, rfl, rfl⟩

section FixedState
variable (st : sch.sched_state)

theorem trans_schedule_policy_focused_user_event (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (e : E.I) (k : E.O e → Thread E B) (x : E.O e)
    (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    trans (.obs (E := E ⊕ₑ schedE) (.inl e) x) (schedule_policy sch (n + 1) v (some i) st)
      (schedule_policy sch (n + 1) (v.set i (k x)) (some i) st) := by
  rw [schedule_policy_focused_user_event_equ sch n v i e k st h]
  exact trans_vis (E := E ⊕ₑ schedE) (e := .inl e) x _

/-- A visible step of the focused thread is a `τ` step of the scheduler. -/
theorem trans_schedule_policy_focused_step (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .step t) :
    trans .tau (schedule_policy sch (n + 1) v (some i) st)
      (schedule_policy sch (n + 1) (v.set i t) (some i) st) := by
  rw [schedule_policy_focused_step_equ sch n v i t st h]
  exact trans_step _

/-- A hidden branch of the focused thread is crawled by the scheduler. -/
theorem trans_schedule_policy_focused_br (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    {c : B.I} (k : B.O c → Thread E B) (j : B.O c) (l : Label (E ⊕ₑ schedE))
    (u : Completed E B) (h : v[i].unfold = .br c k)
    (tr : trans l (schedule_policy sch (n + 1) (v.set i (k j)) (some i) st) u) :
    trans l (schedule_policy sch (n + 1) v (some i) st) u := by
  rw [schedule_policy_focused_br_equ sch n v i k st h]
  exact trans_br j tr

/-- A yield transition of the focused thread lifts every transition of the unfocused pool. -/
theorem schedule_lift_yield (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) (u : Thread E B)
    (tr : trans (.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (.inl ⟨⟩) ⟨⟩) v[i] u) :
    ∀ l q, trans l (schedule_policy sch (n + 1) (v.set i u) none st) q →
      trans l (schedule_policy sch (n + 1) v (some i) st) q := by
  unfold CTree.trans at tr
  generalize hT : v[i].unfold = T at tr
  generalize hl : (Label.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (.inl ⟨⟩) ⟨⟩) = lbl at tr
  induction tr generalizing v with
  | @br _ x k _ _ _ ih =>
    intro l q tq
    refine trans_schedule_policy_focused_br sch st n v i _ x l q hT ?_
    exact ih (v.set i (k x)) (by simp) hl l q (by rwa [Vector.set_set])
  | @guard g _ _ _ ih =>
    intro l q tq
    rw [schedule_policy_focused_guard_equ sch n v i _ st hT]
    exact trans_guard (ih (v.set i g) (by simp) hl l q (by rwa [Vector.set_set]))
  | step => cases hl
  | obs x =>
    cases hl
    intro l q tq
    rw [schedule_policy_focused_yield_equ sch n v i _ st hT]
    exact trans_guard tq
  | val => cases hl

/-- A user event of the focused thread is the same user event of the scheduler. -/
theorem schedule_lift_user (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) (e : E.I)
    (x : E.O e) (u : Thread E B)
    (tr : trans (.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (.inr (.inr e)) x) v[i] u) :
    trans (.obs (E := E ⊕ₑ schedE) (.inl e) x) (schedule_policy sch (n + 1) v (some i) st)
      (schedule_policy sch (n + 1) (v.set i u) (some i) st) := by
  unfold CTree.trans at tr
  generalize hT : v[i].unfold = T at tr
  generalize hl : (Label.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (.inr (.inr e)) x) = lbl at tr
  induction tr generalizing v with
  | @br _ y k _ _ _ ih =>
    refine trans_schedule_policy_focused_br sch st n v i _ y _ _ hT ?_
    have := ih (v.set i (k y)) (by simp) hl
    rwa [Vector.set_set] at this
  | @guard g _ _ _ ih =>
    rw [schedule_policy_focused_guard_equ sch n v i _ st hT]
    have := ih (v.set i g) (by simp) hl
    rw [Vector.set_set] at this
    exact trans_guard this
  | step => cases hl
  | obs y =>
    cases hl
    exact trans_schedule_policy_focused_user_event sch st n v i e _ x hT
  | val => cases hl

/-- A `τ` transition of the focused thread is a `τ` transition of the scheduler. -/
theorem schedule_lift_tau (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) (u : Thread E B)
    (tr : trans .tau v[i] u) :
    trans .tau (schedule_policy sch (n + 1) v (some i) st)
      (schedule_policy sch (n + 1) (v.set i u) (some i) st) := by
  unfold CTree.trans at tr
  generalize hT : v[i].unfold = T at tr
  generalize hl : (Label.tau : Label (yieldE ⊕ₑ forkE ⊕ₑ E)) = lbl at tr
  induction tr generalizing v with
  | @br _ y k _ _ _ ih =>
    refine trans_schedule_policy_focused_br sch st n v i _ y _ _ hT ?_
    have := ih (v.set i (k y)) (by simp) hl
    rwa [Vector.set_set] at this
  | @guard g _ _ _ ih =>
    rw [schedule_policy_focused_guard_equ sch n v i _ st hT]
    have := ih (v.set i g) (by simp) hl
    rw [Vector.set_set] at this
    exact trans_guard this
  | step => exact trans_schedule_policy_focused_step sch st n v i _ hT
  | obs => cases hl
  | val => cases hl

/-- A fork transition of the focused thread: both fork answers are available at the same node,
and every transition of the forked pool lifts. -/
theorem schedule_lift_fork (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) (b : Bool)
    (u : Thread E B) (tr : trans (.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (.inr (.inl ⟨⟩)) b) v[i] u) :
    ∃ k2 : Bool → Thread E B,
      (∀ c, trans (.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (.inr (.inl ⟨⟩)) c) v[i] (k2 c)) ∧
      ∀ l q, trans l (schedule_policy sch (n + 2) (Vector.cons (k2 true) (v.set i (k2 false)))
          (some i.succ) st) q →
        trans l (schedule_policy sch (n + 1) v (some i) st) q := by
  unfold CTree.trans at tr
  generalize hT : v[i].unfold = T at tr
  generalize hl : (Label.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (.inr (.inl ⟨⟩)) b) = lbl at tr
  induction tr generalizing v with
  | @br _ x k _ _ _ ih =>
    obtain ⟨k2, hc, hs⟩ := ih (v.set i (k x)) (by simp) hl
    refine ⟨k2, fun c => ?_, fun l q tq => ?_⟩
    · have := hc c
      rw [show (v.set i (k x))[i] = k x by simp] at this
      unfold CTree.trans; rw [hT]; exact .br x this
    · refine trans_schedule_policy_focused_br sch st n v i _ x l q hT (hs l q ?_)
      rwa [Vector.set_set]
  | @guard g _ _ _ ih =>
    obtain ⟨k2, hc, hs⟩ := ih (v.set i g) (by simp) hl
    refine ⟨k2, fun c => ?_, fun l q tq => ?_⟩
    · have := hc c
      rw [show (v.set i g)[i] = g by simp] at this
      unfold CTree.trans; rw [hT]; exact .guard this
    · rw [schedule_policy_focused_guard_equ sch n v i _ st hT]
      refine trans_guard (hs l q ?_)
      rwa [Vector.set_set]
  | step => cases hl
  | @obs e k x =>
    cases hl
    refine ⟨k, fun c => ?_, fun l q tq => ?_⟩
    · unfold CTree.trans; rw [hT]; exact .obs c
    · rw [schedule_policy_focused_fork_equ sch n v i k st hT]
      exact trans_guard tq
  | val => cases hl

/-- A return of the focused thread lifts every transition of the shrunk unfocused pool. -/
theorem schedule_lift_ret (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) (u : Thread E B)
    (tr : trans (.val (⟨⟩ : PUnit) : Label (yieldE ⊕ₑ forkE ⊕ₑ E)) v[i] u) :
    ∀ l t', trans l (schedule_policy sch n (v.eraseIdx i) none st) t' →
      trans l (schedule_policy sch (n + 1) v (some i) st) t' := by
  unfold CTree.trans at tr
  generalize hT : v[i].unfold = T at tr
  generalize hl : (Label.val (⟨⟩ : PUnit) : Label (yieldE ⊕ₑ forkE ⊕ₑ E)) = lbl at tr
  induction tr generalizing v with
  | @br _ x k _ _ _ ih =>
    intro l q tq
    refine trans_schedule_policy_focused_br sch st n v i _ x l q hT
      (ih (v.set i (k x)) (by simp) hl l q ?_)
    rwa [schedule_policy_pool_proper sch n _ _ none st (remove_replace_pool_equ v i _)]
  | @guard g _ _ _ ih =>
    intro l q tq
    rw [schedule_policy_focused_guard_equ sch n v i _ st hT]
    refine trans_guard (ih (v.set i g) (by simp) hl l q ?_)
    rwa [schedule_policy_pool_proper sch n _ _ none st (remove_replace_pool_equ v i _)]
  | step => cases hl
  | obs => cases hl
  | @val r =>
    intro l q tq
    cases r
    rw [schedule_policy_focused_ret_equ sch n v i st hT]
    exact trans_guard tq

end FixedState

/-- Exact phase shapes of the scheduler bisimulation: a raw scheduler root, a hidden boundary
choice and its selected child (Rocq `schedule_sb_shape`). -/
inductive ScheduleSbShape : Completed E B → Completed E B → Prop
  | shapeAt (n : Nat) (v w : Pool E B n) (f : Option (Fin n)) (st : sch.sched_state) :
      pool_branchfree v → pool_branchfree w → pool_sbisim v w →
      ScheduleSbShape (schedule_policy sch n v f st) (schedule_policy sch n w f st)
  | shapeChoice (n a : Nat) (v w : Pool E B (n + 1))
      (pick : Fin (a + 2) → Fin (n + 1) × sch.sched_state) :
      pool_branchfree v → pool_branchfree w → pool_sbisim v w →
      ScheduleSbShape
        (CTree.brn (a + 2) fun x => .vis (.inr (slot_index (pick x).1))
          fun _ => schedule_policy sch (n + 1) v (some (pick x).1) (pick x).2)
        (CTree.brn (a + 2) fun x => .vis (.inr (slot_index (pick x).1))
          fun _ => schedule_policy sch (n + 1) w (some (pick x).1) (pick x).2)
  | shapeSelected (n : Nat) (v w : Pool E B (n + 1)) (i : Fin (n + 1)) (st : sch.sched_state) :
      pool_branchfree v → pool_branchfree w → pool_sbisim v w →
      ScheduleSbShape
        (.vis (.inr (slot_index i)) fun _ => schedule_policy sch (n + 1) v (some i) st)
        (.vis (.inr (slot_index i)) fun _ => schedule_policy sch (n + 1) w (some i) st)

/-- `ScheduleSbShape` closed under (structural) equality (Rocq `schedule_sb_phase`). -/
inductive ScheduleSbPhase : Completed E B → Completed E B → Prop
  | sbPhaseAt (n : Nat) (v w : Pool E B n) (f : Option (Fin n)) (st : sch.sched_state)
      (T U : Completed E B) :
      pool_branchfree v → pool_branchfree w → pool_sbisim v w →
      T = schedule_policy sch n v f st → U = schedule_policy sch n w f st → ScheduleSbPhase T U
  | sbPhaseChoice (n a : Nat) (v w : Pool E B (n + 1))
      (pick : Fin (a + 2) → Fin (n + 1) × sch.sched_state) (T U : Completed E B) :
      pool_branchfree v → pool_branchfree w → pool_sbisim v w →
      T = (CTree.brn (E := E ⊕ₑ schedE) (a + 2) fun x => .vis (.inr (slot_index (pick x).1))
        fun _ => schedule_policy sch (n + 1) v (some (pick x).1) (pick x).2) →
      U = (CTree.brn (E := E ⊕ₑ schedE) (a + 2) fun x => .vis (.inr (slot_index (pick x).1))
        fun _ => schedule_policy sch (n + 1) w (some (pick x).1) (pick x).2) →
      ScheduleSbPhase T U
  | sbPhaseSelected (n : Nat) (v w : Pool E B (n + 1)) (i : Fin (n + 1)) (st : sch.sched_state)
      (T U : Completed E B) :
      pool_branchfree v → pool_branchfree w → pool_sbisim v w →
      T = (CTree.vis (E := E ⊕ₑ schedE) (.inr (slot_index i))
        fun _ => schedule_policy sch (n + 1) v (some i) st) →
      U = (CTree.vis (E := E ⊕ₑ schedE) (.inr (slot_index i))
        fun _ => schedule_policy sch (n + 1) w (some i) st) →
      ScheduleSbPhase T U

omit [Bn -< B] in
private theorem trans_of_unfold {F : Effect.{0}} {X : Type} {t t' : CTree F B X}
    {T : CTreeF F B X (CTree F B X)} {l : Label F} (h : t.unfold = T) (tr : Trans_ l T t') :
    trans l t t' := by
  unfold CTree.trans; rw [h]; exact tr

/-- The right tree replays the left branch index, so no lawfulness of `Bn -< B` is needed. -/
private theorem brn_match {F : Effect.{0}} {X : Type} {P : CTree F B X → CTree F B X → Prop}
    (m : Nat) {k k' : Fin m → CTree F B X}
    (h : ∀ a l t', trans l (k a) t' → ∃ u', trans l (k' a) u' ∧ P t' u') {l : Label F}
    {t' : CTree F B X} (tr : trans l (CTree.brn m k) t') :
    ∃ u', trans l (CTree.brn m k') u' ∧ P t' u' := by
  obtain ⟨x, tr⟩ := trans_br_inv tr
  obtain ⟨u', tu, hu⟩ := h _ l t' tr
  exact ⟨u', trans_br x tu, hu⟩

private theorem br_alts_match {F : Effect.{0}} {X : Type} {P : CTree F B X → CTree F B X → Prop}
    (m : Nat) {k k' : Fin (m + 1) → CTree F B X}
    (h : ∀ a l t', trans l (k a) t' → ∃ u', trans l (k' a) u' ∧ P t' u') {l : Label F}
    {t' : CTree F B X} (tr : trans l (br_alts m k) t') :
    ∃ u', trans l (br_alts m k') u' ∧ P t' u' := by
  cases m with
  | zero => exact h 0 l t' tr
  | succ m => exact brn_match (m + 2) h tr

/-- One scheduler transition from a raw root (Rocq `focused_heads` dispatch); `hrec` answers the
transitions under a leading scheduler guard. -/
private theorem schedule_sb_step {R : Rel (Completed E B) (Completed E B)}
    (hR : Chain (sb Eq) R)
    (Hch : ∀ n (v w : Pool E B n) f st, pool_branchfree v → pool_branchfree w →
      pool_sbisim v w → R (schedule_policy sch n v f st) (schedule_policy sch n w f st))
    {l : Label (E ⊕ₑ schedE)} {t' : Completed E B} {n : Nat} {v w : Pool E B n}
    {f : Option (Fin n)} {st : sch.sched_state}
    (bv : pool_branchfree v) (bw : pool_branchfree w) (hp : pool_sbisim v w)
    (hrec : ∀ g, (schedule_policy sch n v f st).unfold = .guard g →
      ∀ n' (v' w' : Pool E B n') f' st', pool_branchfree v' → pool_branchfree w' →
        pool_sbisim v' w' → g = schedule_policy sch n' v' f' st' →
        ∃ u', trans l (schedule_policy sch n' w' f' st') u' ∧ R t' u')
    (tr : trans l (schedule_policy sch n v f st) t') :
    ∃ u', trans l (schedule_policy sch n w f st) u' ∧ R t' u' := by
  rcases f with _ | i
  · cases n with
    | zero =>
      rw [schedule_policy_empty_equ] at tr ⊢
      obtain ⟨rfl, rfl⟩ := trans_ret_inv tr
      exact ⟨.stuck, trans_ret _, sb_chain_refl (fun _ => rfl) hR _⟩
    | succ n =>
      rw [schedule_policy_no_focus_equ] at tr ⊢
      refine br_alts_match _ (fun a l t' tr => ?_) tr
      obtain ⟨⟨⟩, rfl, rfl⟩ := trans_vis_inv tr
      exact ⟨_, trans_vis _ _, Hch _ _ _ _ _ bv bw hp⟩
  · cases n with
    | zero => exact i.elim0
    | succ n =>
      rcases hv : v[i].unfold with ⟨⟩ | _ | t0 | g | ⟨e, k⟩ | c
      · -- return: recurse on the smaller pool, the bisimilar slot returns too
        obtain ⟨u', tu, hu⟩ := hrec _ (schedule_policy_focused_ret sch n v i st hv) n _ _ none st
          (pool_branchfree_remove v i bv) (pool_branchfree_remove w i bw)
          (remove_pool_sbisim v w i hp) rfl
        obtain ⟨uv, tv, -⟩ := sbisim_trans_l _ _ _ _ (hp i) (trans_of_unfold hv .val)
        exact ⟨u', schedule_lift_ret sch st n w i uv tv l u' tu, hu⟩
      · rw [schedule_policy_focused_stuck_equ sch n v i st hv] at tr
        exact (trans_stuck_inv tr).elim
      · rw [schedule_policy_focused_step_equ sch n v i t0 st hv] at tr
        obtain ⟨rfl, rfl⟩ := trans_step_inv tr
        have t1 := trans_of_unfold hv .step
        obtain ⟨u', tu, hu⟩ := sbisim_trans_l _ _ _ _ (hp i) t1
        exact ⟨_, schedule_lift_tau sch st n w i u' tu,
          Hch _ _ _ _ _ (pool_branchfree_step v i _ t0 bv t1) (pool_branchfree_step w i _ u' bw tu)
            (replace_pool_sbisim v w i t0 u' hp hu)⟩
      · -- guard: same pool with the guard consumed, focus unchanged
        have bg : BranchFree g := by
          have := (branchfree_unfold _).1 (bv i)
          rw [hv] at this
          cases this with | guard _ h => exact h
        have hvg : v[i] = .guard g := unfold_inj (by rw [hv, unfold_guard])
        have hgw : g ~ w[i] := sbisim_trans (hvg ▸ sbisim_symm (sb_guard g)) (hp i)
        refine hrec _ (schedule_policy_focused_guard sch n v i g st hv) (n + 1) (v.set i g) w
          (some i) st (pool_branchfree_replace v i g bv bg) bw (fun j => ?_) rfl
        have := vector_replace_pointwise (fun a b : Thread E B => a ~ b) v w i g w[i]
          (fun j _ => hp j) hgw j
        simpa using this
      · rcases e with y | f | e
        · -- yield: consumed without a transition, the bisimilar slot yields too
          cases y
          have ty := trans_of_unfold hv (.obs PUnit.unit)
          obtain ⟨uy, tuy, huy⟩ := sbisim_trans_l _ _ _ _ (hp i) ty
          obtain ⟨u', tu, hu⟩ := hrec _ (schedule_policy_focused_yield sch n v i _ st hv) (n + 1)
            (v.set i _) (w.set i uy) none st
            (pool_branchfree_step v i _ _ bv ty) (pool_branchfree_step w i _ _ bw tuy)
            (replace_pool_sbisim v w i _ _ hp huy) rfl
          exact ⟨u', schedule_lift_yield sch st n w i uy tuy l u' tu, hu⟩
        · -- fork: both answers are reconstructed at the same source node
          cases f
          have tf := trans_of_unfold hv (.obs false)
          obtain ⟨uf, tuf, -⟩ := sbisim_trans_l _ _ _ _ (hp i) tf
          obtain ⟨kf, hkf, lift⟩ := schedule_lift_fork sch st n w i false uf tuf
          have hvk : v[i] = .vis (.inr (.inl ⟨⟩)) k := unfold_inj (by rw [hv, unfold_vis])
          have sk : ∀ c, k c ~ kf c := fun c => by
            obtain ⟨wc, tc, hc⟩ := sbisim_trans_l _ _ _ _ (sbisim_symm (hp i)) (hkf c)
            rw [hvk] at tc
            obtain ⟨y, rfl, hl⟩ := trans_vis_inv tc
            obtain rfl := eq_of_heq (obs_eq_inv hl).2
            exact sbisim_symm hc
          have bk : ∀ c, BranchFree (k c) := fun c =>
            branchfree_trans _ _ _ (bv i) (trans_of_unfold hv (.obs c))
          have bkf : ∀ c, BranchFree (kf c) := fun c => branchfree_trans _ _ _ (bw i) (hkf c)
          obtain ⟨u', tu, hu⟩ := hrec _ (schedule_policy_focused_fork sch n v i k st hv) (n + 2)
            (Vector.cons (k true) (v.set i (k false))) (Vector.cons (kf true) (w.set i (kf false)))
            (some i.succ) st
            (pool_branchfree_cons _ _ (bk true) (pool_branchfree_replace _ _ _ bv (bk false)))
            (pool_branchfree_cons _ _ (bkf true) (pool_branchfree_replace _ _ _ bw (bkf false)))
            (cons_pool_sbisim _ _ _ _ (sk true) (replace_pool_sbisim _ _ _ _ _ hp (sk false))) rfl
          exact ⟨u', lift l u' tu, hu⟩
        · -- user event: the same event on both sides
          rw [schedule_policy_focused_user_event_equ sch n v i e k st hv] at tr
          obtain ⟨x, rfl, rfl⟩ := trans_vis_inv tr
          have tx := trans_of_unfold hv
            (Trans_.obs (E := yieldE ⊕ₑ forkE ⊕ₑ E) (e := .inr (.inr e)) x)
          obtain ⟨u', tu, hu⟩ := sbisim_trans_l _ _ _ _ (hp i) tx
          exact ⟨_, schedule_lift_user sch st n w i e x u' tu,
            Hch _ _ _ _ _ (pool_branchfree_step _ _ _ _ bv tx) (pool_branchfree_step _ _ _ _ bw tu)
              (replace_pool_sbisim _ _ _ _ _ hp hu)⟩
      · -- a hidden branch contradicts branch freedom (Rocq `branchfree_absurd`)
        have := (branchfree_unfold _).1 (bv i)
        rw [hv] at this
        cases this

/-- `schedule_sb_step` closed by induction on the scheduler transition. -/
private theorem schedule_sb_at_match {R : Rel (Completed E B) (Completed E B)}
    (hR : Chain (sb Eq) R)
    (Hch : ∀ n (v w : Pool E B n) f st, pool_branchfree v → pool_branchfree w →
      pool_sbisim v w → R (schedule_policy sch n v f st) (schedule_policy sch n w f st))
    {l : Label (E ⊕ₑ schedE)} {T : CTreeF (E ⊕ₑ schedE) B PUnit (Completed E B)}
    {t' : Completed E B} (tr : Trans_ l T t') :
    ∀ n (v w : Pool E B n) f st, pool_branchfree v → pool_branchfree w → pool_sbisim v w →
      T = (schedule_policy sch n v f st).unfold →
      ∃ u', trans l (schedule_policy sch n w f st) u' ∧ R t' u' := by
  induction tr with
  | br x tr =>
    intro n v w f st bv bw hp hT
    exact schedule_sb_step sch hR Hch bv bw hp (fun g hg => by rw [← hT] at hg; cases hg)
      (trans_of_unfold hT.symm (.br x tr))
  | guard tr ih =>
    intro n v w f st bv bw hp hT
    refine schedule_sb_step sch hR Hch bv bw hp
      (fun g hg n' v' w' f' st' bv' bw' hp' hg' => ?_) (trans_of_unfold hT.symm (.guard tr))
    rw [← hT] at hg
    injection hg with hg
    subst hg hg'
    exact ih n' v' w' f' st' bv' bw' hp' rfl
  | step =>
    intro n v w f st bv bw hp hT
    exact schedule_sb_step sch hR Hch bv bw hp (fun g hg => by rw [← hT] at hg; cases hg)
      (trans_of_unfold hT.symm .step)
  | obs x =>
    intro n v w f st bv bw hp hT
    exact schedule_sb_step sch hR Hch bv bw hp (fun g hg => by rw [← hT] at hg; cases hg)
      (trans_of_unfold hT.symm (.obs x))
  | val =>
    intro n v w f st bv bw hp hT
    exact schedule_sb_step sch hR Hch bv bw hp (fun g hg => by rw [← hT] at hg; cases hg)
      (trans_of_unfold hT.symm .val)

/-- Every transition of the left side of a phase shape is answered by the right side, up to the
chain `R` of the bisimulation (Rocq states it on `trans_` and observations). -/
theorem schedule_sb_shape_match {R : Rel (Completed E B) (Completed E B)}
    (hR : Chain (sb Eq) R)
    (Hch : ∀ n (v w : Pool E B n) f st, pool_branchfree v → pool_branchfree w →
      pool_sbisim v w → R (schedule_policy sch n v f st) (schedule_policy sch n w f st)) :
    ∀ l (T : CTreeF (E ⊕ₑ schedE) B PUnit (Completed E B)) t', Trans_ l T t' →
      ∀ t u, T = t.unfold → ScheduleSbShape sch t u → ∃ u', trans l u u' ∧ R t' u' := by
  intro l T t' tr t u hT hs
  have tr' : trans l t t' := trans_of_unfold hT.symm tr
  cases hs with
  | shapeAt n v w f st bv bw hp => exact schedule_sb_at_match sch hR Hch tr n v w f st bv bw hp hT
  | shapeChoice n a v w pick bv bw hp =>
    refine brn_match _ (fun x l t' tr => ?_) tr'
    obtain ⟨⟨⟩, rfl, rfl⟩ := trans_vis_inv tr
    exact ⟨_, trans_vis _ _, Hch _ _ _ _ _ bv bw hp⟩
  | shapeSelected n v w i st bv bw hp =>
    obtain ⟨⟨⟩, rfl, rfl⟩ := trans_vis_inv tr'
    exact ⟨_, trans_vis _ _, Hch _ _ _ _ _ bv bw hp⟩

theorem schedule_sb_phase_match {R : Rel (Completed E B) (Completed E B)}
    (hR : Chain (sb Eq) R)
    (Hch : ∀ n (v w : Pool E B n) f st, pool_branchfree v → pool_branchfree w →
      pool_sbisim v w → R (schedule_policy sch n v f st) (schedule_policy sch n w f st))
    (T U : Completed E B) (l : Label (E ⊕ₑ schedE)) (q : Completed E B)
    (hP : ScheduleSbPhase sch T U) (tr : trans l T q) : ∃ u, trans l U u ∧ R q u := by
  rcases hP with ⟨n, v, w, f, st, _, _, bv, bw, hp, rfl, rfl⟩ |
    ⟨n, a, v, w, pick, _, _, bv, bw, hp, rfl, rfl⟩ | ⟨n, v, w, i, st, _, _, bv, bw, hp, rfl, rfl⟩
  · exact schedule_sb_shape_match sch hR Hch l _ q tr _ _ rfl (.shapeAt n v w f st bv bw hp)
  · exact schedule_sb_shape_match sch hR Hch l _ q tr _ _ rfl
      (.shapeChoice n a v w pick bv bw hp)
  · exact schedule_sb_shape_match sch hR Hch l _ q tr _ _ rfl
      (.shapeSelected n v w i st bv bw hp)

/-- **Scheduler congruence.** The same policy, focus and state over pointwise bisimilar
branch-free pools give bisimilar scheduled trees. -/
theorem sbisim_schedule_policy (n : Nat) (v1 v2 : Pool E B n) (focus : Option (Fin n))
    (st : sch.sched_state) (b1 : pool_branchfree v1) (b2 : pool_branchfree v2)
    (p : pool_sbisim v1 v2) :
    schedule_policy sch n v1 focus st ~ schedule_policy sch n v2 focus st := by
  refine coinduction (b := sb Eq)
    (ι := (n : Nat) ×' (v1 : Pool E B n) ×' (v2 : Pool E B n) ×' (_ : Option (Fin n)) ×'
      (_ : sch.sched_state) ×' (pool_branchfree v1 ∧ pool_branchfree v2 ∧ pool_sbisim v1 v2))
    (fun i => schedule_policy sch i.1 i.2.1 i.2.2.2.1 i.2.2.2.2.1)
    (fun i => schedule_policy sch i.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1) ?_
    ⟨n, v1, v2, focus, st, b1, b2, p⟩
  rintro R hR CIH ⟨n, v1, v2, focus, st, b1, b2, p⟩
  have Hch : ∀ n (v w : Pool E B n) f st, pool_branchfree v → pool_branchfree w →
      pool_sbisim v w → R (schedule_policy sch n v f st) (schedule_policy sch n w f st) :=
    fun n v w f st bv bw hp => CIH ⟨n, v, w, f, st, bv, bw, hp⟩
  refine ⟨fun l q tr => ?_, fun l q tr => ?_⟩
  · obtain ⟨u, tu, hu⟩ := schedule_sb_phase_match sch hR Hch _ _ l q
      (.sbPhaseAt n v1 v2 focus st _ _ b1 b2 p rfl rfl) tr
    exact ⟨l, u, tu, hu, rfl⟩
  · obtain ⟨u, tu, hu⟩ := schedule_sb_phase_match sch hR Hch _ _ l q
      (.sbPhaseAt n v2 v1 focus st _ _ b2 b1 (pool_sbisim_sym _ _ p) rfl rfl) tr
    exact ⟨l, u, tu, sb_chain_symm (fun _ _ h => h.symm) hR _ _ hu, rfl⟩

end SchedulerTransitions

section SchedulerSpecializations
variable {E B : Effect.{0}} [Bn -< B]

theorem trans_schedule_empty_ret (v : Pool E B 0) : schedule 0 v none = .ret ⟨⟩ :=
  schedule_policy_empty_equ nd_scheduler v ⟨⟩

theorem trans_schedule_focused_ret (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .ret ⟨⟩) :
    schedule (n + 1) v (some i) = .guard (schedule n (v.eraseIdx i) none) :=
  schedule_policy_focused_ret_equ nd_scheduler n v i ⟨⟩ h

theorem trans_schedule_focused_stuck (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .stuck) : schedule (n + 1) v (some i) = .stuck :=
  schedule_policy_focused_stuck_equ nd_scheduler n v i ⟨⟩ h

theorem trans_schedule_focused_guard (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .guard t) :
    schedule (n + 1) v (some i) = .guard (schedule (n + 1) (v.set i t) (some i)) :=
  schedule_policy_focused_guard_equ nd_scheduler n v i t ⟨⟩ h

theorem schedule_focused_step_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .step t) :
    schedule (n + 1) v (some i) = .step (schedule (n + 1) (v.set i t) (some i)) :=
  schedule_policy_focused_step_equ nd_scheduler n v i t ⟨⟩ h

theorem schedule_focused_br_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) {c : B.I}
    (k : B.O c → Thread E B) (h : v[i].unfold = .br c k) :
    schedule (n + 1) v (some i) = .br c fun j => schedule (n + 1) (v.set i (k j)) (some i) :=
  schedule_policy_focused_br_equ nd_scheduler n v i k ⟨⟩ h

theorem schedule_no_focus_equ (n : Nat) (v : Pool E B (n + 1)) :
    schedule (n + 1) v none = match n, v with
      | 0, v => .vis (.inr (0 : Nat)) fun _ => schedule 1 v (some 0)
      | m + 1, v => CTree.brn (m + 2) fun i =>
          .vis (.inr (slot_index i)) fun _ => schedule (m + 2) v (some i) :=
  schedule_no_focus_nonempty n v

theorem schedule_pool_proper (n : Nat) (v w : Pool E B n) (focus : Option (Fin n))
    (h : pool_equ v w) : schedule n v focus = schedule n w focus :=
  schedule_policy_pool_proper nd_scheduler n v w focus ⟨⟩ h

theorem schedule_rr_pool_proper (n : Nat) (v w : Pool E B n) (focus : Option (Fin n))
    (cursor : Nat) (h : pool_equ v w) :
    schedule_rr n v focus cursor = schedule_rr n w focus cursor :=
  schedule_policy_pool_proper rr_scheduler n v w focus cursor h

theorem sbisim_schedule (n : Nat) (v w : Pool E B n) (focus : Option (Fin n))
    (bv : pool_branchfree v) (bw : pool_branchfree w) (h : pool_sbisim v w) :
    schedule n v focus ~ schedule n w focus :=
  sbisim_schedule_policy nd_scheduler n v w focus ⟨⟩ bv bw h

theorem sbisim_schedule_rr (n : Nat) (v w : Pool E B n) (focus : Option (Fin n)) (cursor : Nat)
    (bv : pool_branchfree v) (bw : pool_branchfree w) (h : pool_sbisim v w) :
    schedule_rr n v focus cursor ~ schedule_rr n w focus cursor :=
  sbisim_schedule_policy rr_scheduler n v w focus cursor bv bw h

theorem trans_schedule_focused_yield (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E B) (l : Label (E ⊕ₑ schedE)) (q : Completed E B)
    (h : v[i].unfold = .vis (.inl ⟨⟩) k) (tr : trans l (schedule (n + 1) (v.set i (k ⟨⟩)) none) q) :
    trans l (schedule (n + 1) v (some i)) q := by
  unfold schedule
  rw [schedule_policy_focused_yield_equ nd_scheduler n v i k ⟨⟩ h]
  exact trans_guard tr

theorem trans_schedule_focused_fork (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E B) (l : Label (E ⊕ₑ schedE)) (q : Completed E B)
    (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k)
    (tr : trans l (schedule (n + 2) (Vector.cons (k true) (v.set i (k false))) (some i.succ)) q) :
    trans l (schedule (n + 1) v (some i)) q := by
  unfold schedule
  rw [schedule_policy_focused_fork_equ nd_scheduler n v i k ⟨⟩ h]
  exact trans_guard tr

theorem trans_schedule_focused_user_event (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E B) (x : E.O e) (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    trans (.obs (E := E ⊕ₑ schedE) (.inl e) x) (schedule (n + 1) v (some i))
      (schedule (n + 1) (v.set i (k x)) (some i)) :=
  trans_schedule_policy_focused_user_event nd_scheduler ⟨⟩ n v i e k x h

theorem trans_schedule_focused_step (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .step t) :
    trans .tau (schedule (n + 1) v (some i)) (schedule (n + 1) (v.set i t) (some i)) :=
  trans_schedule_policy_focused_step nd_scheduler ⟨⟩ n v i t h

theorem trans_schedule_focused_br (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) {c : B.I}
    (k : B.O c → Thread E B) (j : B.O c) (l : Label (E ⊕ₑ schedE)) (q : Completed E B)
    (h : v[i].unfold = .br c k) (tr : trans l (schedule (n + 1) (v.set i (k j)) (some i)) q) :
    trans l (schedule (n + 1) v (some i)) q :=
  trans_schedule_policy_focused_br nd_scheduler ⟨⟩ n v i k j l q h tr

theorem trans_schedule_no_focus_nonempty [LawfulSubeffect Bn B] (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) :
    trans (.obs (E := E ⊕ₑ schedE) (.inr (slot_index i)) ⟨⟩) (schedule (n + 1) v none)
      (schedule (n + 1) v (some i)) :=
  trans_schedule_policy_no_focus_nonempty nd_scheduler n v ⟨⟩ i

theorem trans_schedule_no_focus_inv (n : Nat) (v : Pool E B (n + 1)) (l : Label (E ⊕ₑ schedE))
    (q : Completed E B) (h : trans l (schedule (n + 1) v none) q) :
    ∃ i, l = .obs (.inr (slot_index i)) ⟨⟩ ∧ q = schedule (n + 1) v (some i) :=
  trans_schedule_policy_no_focus_inv nd_scheduler n v ⟨⟩ l q h

theorem schedule_some_pool_equ {m : Nat} (v w : Pool E B (m + 1)) (i : Fin (m + 1))
    (h : pool_equ v w) : schedule (m + 1) v (some i) = schedule (m + 1) w (some i) :=
  schedule_pool_proper _ v w _ h

theorem br_schedule_pool_equ {n : Nat} (v w : Pool E B (n + 1)) (h : pool_equ v w) :
    CTree.brSn (n + 1) (fun j => schedule (n + 1) v (some j)) =
      CTree.brSn (n + 1) (fun j => schedule (n + 1) w (some j)) :=
  congrArg _ (funext fun j => schedule_pool_proper _ v w (some j) h)

end SchedulerSpecializations

end Tisl.Yield

-- Not ported: Rocq local Ltac `branchfree_absurd` and `focused_heads` (inlined in the private
-- `schedule_sb_step`, which with the private `schedule_sb_at_match`, `brn_match`,
-- `br_alts_match`, `trans_of_unfold` restructures the `trans_` induction of
-- `schedule_sb_shape_match`); abbreviations `Yield_`, `Fork_`, `completed'`, `sbC`.
