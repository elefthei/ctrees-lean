/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.RoundRobin
public import Logic.Yield.Nondeterministic
public import Logic.CTree.Trace
public import Logic.Utils.Vectors

/-!
# First-yield thread segments

One finite derivation `ThreadSegment handler R t σ logs t' σ'` runs a thread up to its first source
`yield`. The user-event premise relates the handler's actual response to a finite emission prefix
by an arbitrary `R` (used at `~` and at `=`; `ThreadSegment_mono` transports between them). Also:
inversion, determinism, and the scheduler laws turning a focused segment into its logs
(← `CTree/Interp/Yield/Segments.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree
open ITree (Effect)

/-- Raw equivalence is bisimilarity. -/
theorem equ_sbisim {E B : Effect.{u}} {X : Type u} (t u : CTree E B X) (h : t = u) : t ~ u :=
  h ▸ sbisim_refl t

/-- `Fork` answers in `Bool`, `Yield` in `Unit`: the two answer types differ. -/
theorem bool_neq_unit (h : @Eq Type Bool Unit) : False := by
  have : ∀ x y : Unit, x = y := fun _ _ => rfl
  rw [← h] at this
  exact Bool.noConfusion (this true false)

section ThreadSegments
variable {E B : Effect.{0}} {W Sg : Type}

/-- First-yield segments: a finite derivation that stops at the first source `yield`. The
handler premise of `user` is the handler's actual effect, related to a finite emission prefix by
`R`; raw thread endpoints are taken up to `=` (`equ`). -/
inductive ThreadSegment (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))
    (R : (Y : Type) → ctreeW W B Y → ctreeW W B Y → Prop) :
    Thread E B → Sg → List W → Thread E B → Sg → Prop
  | yield (k : PUnit → Thread E B) (σ : Sg) :
      ThreadSegment handler R (.vis (.inl ⟨⟩) k) σ [] (k ⟨⟩) σ
  | guard {t : Thread E B} {σ : Sg} {logs : List W} {t' : Thread E B} {σ' : Sg} :
      ThreadSegment handler R t σ logs t' σ' → ThreadSegment handler R (.guard t) σ logs t' σ'
  | user (e : E.I) (k : E.O e → Thread E B) (σ : Sg) (result : E.O e) (σ1 : Sg)
      (before after : List W) (t' : Thread E B) (σ' : Sg) :
      R _ (handler e σ) (emit_list before (pure (result, σ1))) →
      ThreadSegment handler R (k result) σ1 after t' σ' →
      ThreadSegment handler R (.vis (.inr (.inr e)) k) σ (before ++ after) t' σ'
  | equ {t u : Thread E B} {σ : Sg} {logs : List W} {u' t' : Thread E B} {σ' : Sg} :
      t = u → ThreadSegment handler R u σ logs u' σ' → u' = t' →
      ThreadSegment handler R t σ logs t' σ'

variable (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))
  (R : (Y : Type) → ctreeW W B Y → ctreeW W B Y → Prop)

theorem ThreadSegment_equ_input (t u : Thread E B) (σ : Sg) (xs : List W) (residual : Thread E B)
    (σ' : Sg) (heq : t = u) (h : ThreadSegment handler R t σ xs residual σ') :
    ThreadSegment handler R u σ xs residual σ' :=
  heq ▸ h

theorem ThreadSegment_equ_output (t : Thread E B) (σ : Sg) (xs : List W)
    (residual residual' : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ')
    (heq : residual = residual') : ThreadSegment handler R t σ xs residual' σ' :=
  heq ▸ h

theorem ThreadSegment_yield_inv_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ∀ k : PUnit → Thread E B, t = .vis (.inl ⟨⟩) k → xs = [] ∧ σ' = σ ∧ k ⟨⟩ = residual := by
  induction h with
  | yield =>
    intro k heq
    cases (vis_eq_vis_iff'.1 heq).2
    exact ⟨rfl, rfl, rfl⟩
  | guard => intro k heq; simp at heq
  | user => intro k heq; simp [vis_eq_vis_iff'] at heq
  | equ htu _ hout ih => intro k heq; subst htu hout; exact ih k heq

theorem ThreadSegment_yield_inv (k : PUnit → Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg)
    (h : ThreadSegment handler R (.vis (.inl ⟨⟩) k) σ xs residual σ') :
    xs = [] ∧ σ' = σ ∧ k ⟨⟩ = residual :=
  ThreadSegment_yield_inv_equ handler R _ σ xs residual σ' h k rfl

theorem ThreadSegment_guard_inv_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ∀ u, t = .guard u → ThreadSegment handler R u σ xs residual σ' := by
  induction h with
  | yield => intro u heq; simp at heq
  | guard h _ => intro u heq; cases guard_eq_guard_iff.1 heq; exact h
  | user => intro u heq; simp at heq
  | equ htu _ hout ih => intro u heq; subst htu hout; exact ih u heq

theorem ThreadSegment_guard_inv (t : Thread E B) (σ : Sg) (xs : List W) (residual : Thread E B)
    (σ' : Sg) (h : ThreadSegment handler R (.guard t) σ xs residual σ') :
    ThreadSegment handler R t σ xs residual σ' :=
  ThreadSegment_guard_inv_equ handler R _ σ xs residual σ' h t rfl

theorem ThreadSegment_user_inv_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ∀ (e : E.I) (k : E.O e → Thread E B), t = .vis (.inr (.inr e)) k →
      ∃ result σ1 before after, xs = before ++ after ∧
        R _ (handler e σ) (emit_list before (pure (result, σ1))) ∧
        ThreadSegment handler R (k result) σ1 after residual σ' := by
  induction h with
  | yield => intro e k heq; simp [vis_eq_vis_iff'] at heq
  | guard => intro e k heq; simp at heq
  | user e0 k0 σ0 result σ1 before after t' σ'' hR hseg =>
    intro e k heq
    obtain ⟨he, hk⟩ := vis_eq_vis_iff'.1 heq
    cases he
    cases hk
    exact ⟨result, σ1, before, after, rfl, hR, hseg⟩
  | equ htu _ hout ih => intro e k heq; subst htu hout; exact ih e k heq

theorem ThreadSegment_user_inv (e : E.I) (k : E.O e → Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg)
    (h : ThreadSegment handler R (.vis (.inr (.inr e)) k) σ xs residual σ') :
    ∃ result σ1 before after, xs = before ++ after ∧
      R _ (handler e σ) (emit_list before (pure (result, σ1))) ∧
      ThreadSegment handler R (k result) σ1 after residual σ' :=
  ThreadSegment_user_inv_equ handler R _ σ xs residual σ' h e k rfl

/-- A derivation starts at a yield, a guard or a user event. -/
theorem ThreadSegment_head (t : Thread E B) (σ : Sg) (xs : List W) (residual : Thread E B)
    (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    (∃ k : PUnit → Thread E B, t = .vis (.inl ⟨⟩) k) ∨ (∃ u, t = .guard u) ∨
      (∃ (e : E.I) (k : E.O e → Thread E B), t = .vis (.inr (.inr e)) k) := by
  induction h with
  | yield k => exact .inl ⟨k, rfl⟩
  | guard => exact .inr (.inl ⟨_, rfl⟩)
  | user e k => exact .inr (.inr ⟨e, k, rfl⟩)
  | equ htu _ _ ih => subst htu; exact ih

/-! Hence a derivation never starts at a return, a fork, a branch, a visible step or a stuck
node. -/

theorem ThreadSegment_ret_absurd_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ¬ t = pure ⟨⟩ := by
  intro heq; subst heq
  rcases ThreadSegment_head handler R _ _ _ _ _ h with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;>
    simp at h'

theorem ThreadSegment_ret_absurd (σ : Sg) (xs : List W) (residual : Thread E B) (σ' : Sg) :
    ¬ ThreadSegment handler R (pure ⟨⟩) σ xs residual σ' :=
  fun h => ThreadSegment_ret_absurd_equ handler R _ σ xs residual σ' h rfl

theorem ThreadSegment_fork_absurd_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ∀ k : Bool → Thread E B, ¬ t = .vis (.inr (.inl ⟨⟩)) k := by
  intro k heq; subst heq
  rcases ThreadSegment_head handler R _ _ _ _ _ h with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;>
    first | simp at h' | (obtain ⟨he, -⟩ := vis_eq_vis_iff'.1 h'; cases he)

theorem ThreadSegment_fork_absurd (k : Bool → Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) :
    ¬ ThreadSegment handler R (.vis (.inr (.inl ⟨⟩)) k) σ xs residual σ' :=
  fun h => ThreadSegment_fork_absurd_equ handler R _ σ xs residual σ' h k rfl

theorem ThreadSegment_br_absurd_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ∀ (c : B.I) (k : B.O c → Thread E B), ¬ t = .br c k := by
  intro c k heq; subst heq
  rcases ThreadSegment_head handler R _ _ _ _ _ h with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;>
    simp at h'

theorem ThreadSegment_br_absurd (c : B.I) (k : B.O c → Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) : ¬ ThreadSegment handler R (.br c k) σ xs residual σ' :=
  fun h => ThreadSegment_br_absurd_equ handler R _ σ xs residual σ' h c k rfl

theorem ThreadSegment_step_absurd_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ∀ u, ¬ t = .step u := by
  intro u heq; subst heq
  rcases ThreadSegment_head handler R _ _ _ _ _ h with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;>
    simp at h'

theorem ThreadSegment_step_absurd (u : Thread E B) (σ : Sg) (xs : List W) (residual : Thread E B)
    (σ' : Sg) : ¬ ThreadSegment handler R (.step u) σ xs residual σ' :=
  fun h => ThreadSegment_step_absurd_equ handler R _ σ xs residual σ' h u rfl

theorem ThreadSegment_stuck_absurd_equ (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') :
    ¬ t = .stuck := by
  intro heq; subst heq
  rcases ThreadSegment_head handler R _ _ _ _ _ h with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;>
    simp at h'

theorem ThreadSegment_stuck_absurd (σ : Sg) (xs : List W) (residual : Thread E B) (σ' : Sg) :
    ¬ ThreadSegment handler R (.stuck : Thread E B) σ xs residual σ' :=
  fun h => ThreadSegment_stuck_absurd_equ handler R _ σ xs residual σ' h rfl

/-- A finite first-yield derivation has a first raw transition: a user case provides its actual
response as the witness. -/
theorem ThreadSegment_can_step (t : Thread E B) (σ : Sg) (xs : List W) (residual : Thread E B)
    (σ' : Sg) (h : ThreadSegment handler R t σ xs residual σ') : ∃ l u, trans l t u := by
  induction h with
  | yield k =>
    exact ⟨_, _, trans_vis (E := yieldE ⊕ₑ forkE ⊕ₑ E) (e := .inl ⟨⟩) PUnit.unit k⟩
  | guard _ ih => obtain ⟨l, u, tr⟩ := ih; exact ⟨l, u, trans_guard tr⟩
  | user e k _ result =>
    exact ⟨_, _, trans_vis (E := yieldE ⊕ₑ forkE ⊕ₑ E) (e := .inr (.inr e)) result k⟩
  | equ htu _ _ ih => subst htu; exact ih

/-- A divergent guard cannot be unfolded into a finite derivation. -/
theorem ThreadSegment_divergent_absurd (t : Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg) (hdiv : isStuck t) :
    ¬ ThreadSegment handler R t σ xs residual σ' := fun h => by
  obtain ⟨l, u, tr⟩ := ThreadSegment_can_step handler R t σ xs residual σ' h
  exact hdiv l u tr

theorem ThreadSegment_spin_absurd (σ : Sg) (xs : List W) (residual : Thread E B) (σ' : Sg) :
    ¬ ThreadSegment handler R (CTree.spinS : Thread E B) σ xs residual σ' :=
  fun h => ThreadSegment_step_absurd_equ handler R _ σ xs residual σ' h _ unfold_spinS

theorem ThreadSegment_branchfree (t : Thread E B) (σ : Sg) (logs : List W)
    (residual : Thread E B) (σ' : Sg) (h : ThreadSegment handler R t σ logs residual σ')
    (hbf : BranchFree t) : BranchFree residual := by
  induction h with
  | yield =>
    rw [branchfree_unfold, unfold_vis] at hbf
    cases hbf with | vis _ _ hk => exact hk ⟨⟩
  | guard _ ih =>
    rw [branchfree_unfold, unfold_guard] at hbf
    cases hbf with | guard _ ht => exact ih ht
  | user e k _ result _ _ _ _ _ _ _ ih =>
    rw [branchfree_unfold, unfold_vis] at hbf
    cases hbf with | vis _ _ hk => exact ih (hk result)
  | equ htu _ hout ih => subst htu hout; exact ih hbf

/-- Guard transport: forgetting finitely many leading guards preserves segments in both
directions (both directions proved together). -/
theorem guard_equ_segment_iff (t u : Thread E B) (h : guard_equ t u) :
    ∀ σ xs residual σ', ThreadSegment handler R t σ xs residual σ' ↔
      ThreadSegment handler R u σ xs residual σ' := by
  unfold guard_equ at h
  induction h with
  | rel h =>
    rcases h with rfl | rfl
    · exact fun _ _ _ _ => Iff.rfl
    · exact fun σ xs r σ' => ⟨ThreadSegment_guard_inv handler R _ σ xs r σ', .guard⟩
  | refl => exact fun _ _ _ _ => Iff.rfl
  | symm _ ih => exact fun σ xs r σ' => (ih σ xs r σ').symm
  | trans _ _ ih₁ ih₂ => exact fun σ xs r σ' => (ih₁ σ xs r σ').trans (ih₂ σ xs r σ')

theorem guard_equ_segment (t u : Thread E B) (σ : Sg) (xs : List W) (t' : Thread E B) (σ' : Sg)
    (heq : guard_equ t u) (hseg : ThreadSegment handler R t σ xs t' σ') :
    ∃ u', ThreadSegment handler R u σ xs u' σ' ∧ guard_equ t' u' :=
  ⟨t', (guard_equ_segment_iff handler R t u heq σ xs t' σ').1 hseg, guard_equ_equ _ _ rfl⟩

/-- An exact segment may end at a residual differing from its target only by finitely many
leading guards. -/
def segment_to (t : Thread E B) (σ : Sg) (logs : List W) (target : Thread E B) (σ' : Sg) :
    Prop :=
  ∃ residual, ThreadSegment handler R t σ logs residual σ' ∧ guard_equ residual target

theorem segment_to_equ (t u : Thread E B) (σ : Sg) (logs : List W) (target : Thread E B)
    (σ' : Sg) (htu : t = u) (h : segment_to handler R u σ logs target σ') :
    segment_to handler R t σ logs target σ' :=
  htu ▸ h

end ThreadSegments

/-- Weakening the response relation weakens the segment: an exact segment becomes a
bisimulation-mode one (`equ_sbisim` supplies the premise). -/
theorem ThreadSegment_mono {E B : Effect.{0}} {W Sg : Type}
    (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))
    (R R' : (Y : Type) → ctreeW W B Y → ctreeW W B Y → Prop)
    (hmono : ∀ X t u, R X t u → R' X t u) :
    ∀ t σ logs residual σ', ThreadSegment handler R t σ logs residual σ' →
      ThreadSegment handler R' t σ logs residual σ' := by
  intro t σ logs residual σ' h
  induction h with
  | yield => exact .yield _ _
  | guard _ ih => exact .guard ih
  | user e k σ result σ1 before after t' σ' hR _ ih =>
    exact .user e k σ result σ1 before after t' σ' (hmono _ _ _ hR) ih
  | equ htu _ hout ih => exact .equ htu ih hout

/-! ## Scheduling laws

Response uniqueness, determinism and handler-fault exclusion need the response relation to imply
strong bisimulation. -/

section SegmentScheduling
variable {E B : Effect.{0}} {W Sg : Type}
  (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))
  (R : (Y : Type) → ctreeW W B Y → ctreeW W B Y → Prop)
  (HR : ∀ X (t u : ctreeW W B X), R X t u → t ~ u)
include HR

theorem handler_response_unique (e : E.I) (σ : Sg) (result : E.O e) (σ1 : Sg) (before : List W)
    (result' : E.O e) (σ2 : Sg) (before' : List W)
    (h1 : R _ (handler e σ) (emit_list before (pure (result, σ1))))
    (h2 : R _ (handler e σ) (emit_list before' (pure (result', σ2)))) :
    before = before' ∧ result = result' ∧ σ1 = σ2 := by
  obtain ⟨hb, hr⟩ := emit_list_ret_injective (B := B) before before' (result, σ1) (result', σ2)
    (sbisim_trans (sbisim_symm (HR _ _ _ h1)) (HR _ _ _ h2))
  simp only [Prod.mk.injEq] at hr
  exact ⟨hb, hr.1, hr.2⟩

theorem ThreadSegment_fault_absurd (e : E.I) (k : E.O e → Thread E B) (σ : Sg) (xs : List W)
    (residual : Thread E B) (σ' : Sg)
    (hf : handler e σ ~ (.stuck : ctreeW W B (E.O e × Sg))) :
    ¬ ThreadSegment handler R (.vis (.inr (.inr e)) k) σ xs residual σ' := fun h => by
  obtain ⟨result, σ1, before, after, -, Eh, -⟩ :=
    ThreadSegment_user_inv handler R e k σ xs residual σ' h
  exact emit_list_ret_not_stuck (B := B) before (result, σ1)
    (sbisim_trans (sbisim_symm (HR _ _ _ Eh)) hf)

theorem ThreadSegment_deterministic (t : Thread E B) (σ : Sg) (xs : List W) (u : Thread E B)
    (σ1 : Sg) (ys : List W) (v : Thread E B) (σ2 : Sg)
    (h1 : ThreadSegment handler R t σ xs u σ1) (h2 : ThreadSegment handler R t σ ys v σ2) :
    xs = ys ∧ σ1 = σ2 ∧ u = v := by
  induction h1 generalizing ys v σ2 with
  | yield k σ0 =>
    obtain ⟨rfl, rfl, rfl⟩ := ThreadSegment_yield_inv handler R k σ0 ys v σ2 h2
    exact ⟨rfl, rfl, rfl⟩
  | guard _ ih => exact ih ys v σ2 (ThreadSegment_guard_inv handler R _ _ ys v σ2 h2)
  | user e k σ0 result σ1' before after _ _ Eh _ ih =>
    obtain ⟨r, σ0', before', after', rfl, Eh', ht⟩ :=
      ThreadSegment_user_inv handler R e k σ0 ys v σ2 h2
    obtain ⟨rfl, rfl, rfl⟩ :=
      handler_response_unique handler R HR e σ0 result σ1' before r σ0' before' Eh Eh'
    obtain ⟨rfl, rfl, rfl⟩ := ih after' v σ2 ht
    exact ⟨rfl, rfl, rfl⟩
  | equ htu _ hout ih => subst htu hout; exact ih ys v σ2 h2

end SegmentScheduling

/-! ## Pool congruence for the focused slot

Pool equivalence is used only for raw `=`; guard removal is restricted to the focused slot. -/

section FocusedCongruenceND
variable {E B : Effect.{0}} [Bn -< B] {W Sg : Type}
  (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))

theorem segment_nd_replace_equ (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1))
    (t u : Thread E B) (focus : Option (Fin (n + 1))) (σ : Sg) (heq : t = u) :
    interp_schedule_nd handler (n + 1) (ts.set i t) focus σ ~
      interp_schedule_nd handler (n + 1) (ts.set i u) focus σ :=
  heq ▸ sbisim_refl _

theorem segment_nd_focused_guard (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (σ : Sg) :
    interp_schedule_nd handler (n + 1) (ts.set i (.guard t)) (some i) σ ~
      interp_schedule_nd handler (n + 1) (ts.set i t) (some i) σ := by
  have := interp_schedule_nd_guard handler n (ts.set i (.guard t)) i t σ (by simp)
  simpa only [Vector.set_set] using this

theorem segment_nd_focused_user (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) (e : E.I)
    (k : E.O e → Thread E B) (σ : Sg) :
    interp_schedule_nd handler (n + 1) (ts.set i (.vis (.inr (.inr e)) k)) (some i) σ ~
      (handler e σ >>= fun p =>
        interp_schedule_nd handler (n + 1) (ts.set i (k p.1)) (some i) p.2) := by
  have := interp_schedule_nd_user handler n (ts.set i (.vis (.inr (.inr e)) k)) i e k σ (by simp)
  simpa only [Vector.set_set] using this

end FocusedCongruenceND

section FocusedCongruencePolicy
variable {E : Effect.{0}} {W Sg : Type} (sch : Scheduler)
  (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem exact_fair_user_replaced (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (e : E.I)
    (k : E.O e → Thread E Bn) (st : sch.sched_state) (σ : Sg) :
    interp_schedule_fair sch handler (n + 1) (ts.set i (.vis (.inr (.inr e)) k)) (some i) st σ =
      (translate relabel_log (handler e σ) >>= fun p =>
        rr_guards 1
          (interp_schedule_fair sch handler (n + 1) (ts.set i (k p.1)) (some i) st p.2)) := by
  rw [interp_schedule_fair_user_exact sch handler n _ i e k st σ (by simp)]
  simp only [Vector.set_set]
  rfl

end FocusedCongruencePolicy

section FocusedCongruenceRR
variable {E : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem segment_rr_replace_equ (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t u : Thread E Bn) (focus : Option (Fin (n + 1))) (m : Nat) (σ : Sg) (heq : t = u) :
    interp_schedule_rr handler (n + 1) (ts.set i t) focus m σ ~
      interp_schedule_rr handler (n + 1) (ts.set i u) focus m σ :=
  segment_fair_replace_equ rr_scheduler handler n ts i t u focus m σ heq

theorem segment_rr_focused_guard (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (m : Nat) (σ : Sg) :
    interp_schedule_rr handler (n + 1) (ts.set i (.guard t)) (some i) m σ ~
      interp_schedule_rr handler (n + 1) (ts.set i t) (some i) m σ :=
  segment_fair_focused_guard rr_scheduler handler n ts i t m σ

theorem segment_rr_focused_user (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (e : E.I)
    (k : E.O e → Thread E Bn) (m : Nat) (σ : Sg) :
    interp_schedule_rr handler (n + 1) (ts.set i (.vis (.inr (.inr e)) k)) (some i) m σ ~
      (translate relabel_log (handler e σ) >>= fun p =>
        interp_schedule_rr handler (n + 1) (ts.set i (k p.1)) (some i) m p.2) :=
  interp_schedule_rr_user_bind handler n ts i _ e k m σ rfl

theorem segment_rr_ret_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (m : Nat)
    (σ : Sg) (hobs : ts[i].unfold = .ret ⟨⟩) :
    interp_schedule_rr handler (n + 1) ts (some i) m σ =
      .guard (interp_schedule_rr handler n (ts.eraseIdx i) none m σ) :=
  interp_schedule_fair_ret_exact rr_scheduler handler n ts i m σ hobs

theorem segment_rr_guard_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .guard t) :
    interp_schedule_rr handler (n + 1) ts (some i) m σ =
      .guard (interp_schedule_rr handler (n + 1) (ts.set i t) (some i) m σ) :=
  interp_schedule_fair_guard_exact rr_scheduler handler n ts i t m σ hobs

theorem segment_rr_yield_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .vis (.inl ⟨⟩) k) :
    interp_schedule_rr handler (n + 1) ts (some i) m σ =
      .guard (interp_schedule_rr handler (n + 1) (ts.set i (k ⟨⟩)) none m σ) :=
  interp_schedule_fair_yield_exact rr_scheduler handler n ts i k m σ hobs

theorem segment_rr_fork_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    interp_schedule_rr handler (n + 1) ts (some i) m σ =
      .guard (interp_schedule_rr handler (n + 2) (Vector.cons (k true) (ts.set i (k false)))
        (some i.succ) m σ) :=
  interp_schedule_fair_fork_exact rr_scheduler handler n ts i k m σ hobs

theorem segment_rr_user_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (e : E.I)
    (k : E.O e → Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .vis (.inr (.inr e)) k) :
    interp_schedule_rr handler (n + 1) ts (some i) m σ =
      (translate relabel_log (handler e σ) >>= fun p =>
        rr_guards 1 (interp_schedule_rr handler (n + 1) (ts.set i (k p.1)) (some i) m p.2)) :=
  interp_schedule_fair_user_exact rr_scheduler handler n ts i e k m σ hobs

theorem segment_rr_select_exact (n : Nat) (ts : Pool E Bn (n + 1)) (m : Nat) (σ : Sg) :
    interp_schedule_rr handler (n + 1) ts none m σ =
      .vis (E := writerE (W ⊕ Nat)) (.inr (slot_index (rr_pick n m))) fun _ =>
        .guard (interp_schedule_rr handler (n + 1) ts (some (rr_pick n m)) (m + 1) σ) :=
  interp_schedule_rr_select_exact handler n ts m σ

theorem exact_rr_user_replaced (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (e : E.I)
    (k : E.O e → Thread E Bn) (m : Nat) (σ : Sg) :
    interp_schedule_rr handler (n + 1) (ts.set i (.vis (.inr (.inr e)) k)) (some i) m σ =
      (translate relabel_log (handler e σ) >>= fun p =>
        rr_guards 1 (interp_schedule_rr handler (n + 1) (ts.set i (k p.1)) (some i) m p.2)) :=
  exact_fair_user_replaced rr_scheduler handler n ts i e k m σ

end FocusedCongruenceRR

/-! ## A focused segment is its logs followed by the unfocused pool -/

section SegmentInterpretationND
variable {E B : Effect.{0}} [Bn -< B] {W Sg : Type}
  (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))
  (R : (Y : Type) → ctreeW W B Y → ctreeW W B Y → Prop)
  (HR : ∀ X (t u : ctreeW W B X), R X t u → t ~ u)
include HR

theorem segment_interp_nd (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) (σ : Sg)
    (xs : List W) (residual : Thread E B) (σ' : Sg)
    (hseg : ThreadSegment handler R ts[i] σ xs residual σ') :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      emit_list xs (interp_schedule_nd handler (n + 1) (ts.set i residual) none σ') := by
  have gen : ∀ t s0 ys r0 s1, ThreadSegment handler R t s0 ys r0 s1 →
      ∀ p (us : Pool E B (p + 1)) (j : Fin (p + 1)),
        interp_schedule_nd handler (p + 1) (us.set j t) (some j) s0 ~
          emit_list ys (interp_schedule_nd handler (p + 1) (us.set j r0) none s1) := by
    intro t s0 ys r0 s1 h
    induction h with
    | yield k σ0 =>
      intro p us j
      have := interp_schedule_nd_yield handler p (us.set j (.vis (.inl ⟨⟩) k)) j k σ0 (by simp)
      simpa only [Vector.set_set, emit_list_nil] using this
    | guard _ ih =>
      exact fun p us j => sbisim_trans (segment_nd_focused_guard handler p us j _ _) (ih p us j)
    | user e k σ0 result σ1 before after _ _ Eh _ ih =>
      intro p us j
      refine sbisim_trans (segment_nd_focused_user handler p us j e k σ0) ?_
      refine sbisim_trans (sbisim_clo_bind_eq (HR _ _ _ Eh) fun _ => sbisim_refl _) ?_
      rw [emit_list_ret_bind, emit_list_app]
      exact emit_list_sbisim _ (ih p us j)
    | equ htu _ hout ih => subst htu hout; exact ih
  have := gen _ _ _ _ _ hseg n ts i
  rwa [interp_schedule_nd_equ handler _ _ _ _ _ (pool_replace_current ts i)] at this

/-- A first-yield segment of slot `i` is one scheduler choice followed by its logs. -/
theorem segment_scheduler_steps [LawfulSubeffect Bn B] {n : Nat} (ts : Pool E B (n + 1)) (σ : Sg)
    (i : Fin (n + 1)) (logs : List W) (residual : Thread E B) (σ' : Sg) (ts' : Pool E B (n + 1))
    (hseg : ThreadSegment handler R ts[i] σ logs residual σ')
    (hpool : pool_equ ts' (ts.set i residual)) :
    ∃ next, FiniteSteps (interp_schedule_nd handler (n + 1) ts none σ)
        (.tau :: logs.map fun o => .obs (E := writerE W) o ⟨⟩) next ∧
      next ~ interp_schedule_nd handler (n + 1) ts' none σ' := by
  have hfoc : interp_schedule_nd handler (n + 1) ts (some i) σ ~
      emit_list logs (interp_schedule_nd handler (n + 1) ts' none σ') := by
    rw [interp_schedule_nd_equ handler _ ts' _ _ _ hpool]
    exact segment_interp_nd handler R HR n ts i σ logs residual σ' hseg
  have hbr : trans .tau
      (CTree.brSn (n + 1) fun j => interp_schedule_nd handler (n + 1) ts (some j) σ)
      (interp_schedule_nd handler (n + 1) ts (some i) σ) :=
    trans_brS' (B₁ := Bn) (c := ⟨n + 1⟩)
      (fun x => interp_schedule_nd handler (n + 1) ts (some x.down) σ) ⟨i⟩
  obtain ⟨focused, hchoose, hfocus⟩ :=
    sbisim_trans_l _ _ _ .tau (sbisim_symm (interp_schedule_nd_select handler n ts σ)) hbr
  obtain ⟨next, hlogs, hnext⟩ := finite_steps_sbisim (finite_steps_emit_list logs _) focused
    (sbisim_trans (sbisim_symm hfoc) hfocus)
  exact ⟨next, .cons hchoose hlogs, sbisim_symm hnext⟩

end SegmentInterpretationND

section SegmentInterpretationPolicy
variable {E : Effect.{0}} {W Sg : Type} (sch : Scheduler)
  (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))
  (R : (Y : Type) → ctreeW W Bn Y → ctreeW W Bn Y → Prop)
  (HR : ∀ X (t u : ctreeW W Bn X), R X t u →
    translate relabel_log t ~ translate relabel_log u)
include HR

theorem segment_interp_fair (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (st : sch.sched_state) (σ : Sg) (xs : List W) (residual : Thread E Bn) (σ' : Sg)
    (hseg : ThreadSegment handler R ts[i] σ xs residual σ') :
    interp_schedule_fair sch handler (n + 1) ts (some i) st σ ~
      emit_list (xs.map .inl)
        (interp_schedule_fair sch handler (n + 1) (ts.set i residual) none st σ') := by
  have gen : ∀ t s0 ys r0 s1, ThreadSegment handler R t s0 ys r0 s1 →
      ∀ p (us : Pool E Bn (p + 1)) (j : Fin (p + 1)),
        interp_schedule_fair sch handler (p + 1) (us.set j t) (some j) st s0 ~
          emit_list (ys.map .inl)
            (interp_schedule_fair sch handler (p + 1) (us.set j r0) none st s1) := by
    intro t s0 ys r0 s1 h
    induction h with
    | yield k σ0 =>
      intro p us j
      have := interp_schedule_fair_yield sch handler p (us.set j (.vis (.inl ⟨⟩) k)) j k st σ0
        (by simp)
      simpa only [Vector.set_set, List.map_nil, emit_list_nil] using this
    | guard _ ih =>
      exact fun p us j =>
        sbisim_trans (segment_fair_focused_guard sch handler p us j _ st _) (ih p us j)
    | user e k σ0 result σ1 before after _ _ Eh _ ih =>
      intro p us j
      refine sbisim_trans (interp_schedule_fair_user_bind sch handler p us j _ e k st σ0 rfl) ?_
      refine sbisim_trans (sbisim_clo_bind_eq (HR _ _ _ Eh) fun _ => sbisim_refl _) ?_
      rw [translate_emit_list, translate_ret, emit_list_ret_bind, List.map_append, emit_list_app]
      exact emit_list_sbisim _ (ih p us j)
    | equ htu _ hout ih => subst htu hout; exact ih
  have := gen _ _ _ _ _ hseg n ts i
  rwa [interp_schedule_fair_equ sch handler _ _ _ _ _ _ (pool_replace_current ts i)] at this

end SegmentInterpretationPolicy

section SegmentInterpretationRR
variable {E : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))
  (R : (Y : Type) → ctreeW W Bn Y → ctreeW W Bn Y → Prop)
  (HR : ∀ X (t u : ctreeW W Bn X), R X t u → t ~ u)
include HR

theorem segment_interp_rr (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (m : Nat)
    (σ : Sg) (xs : List W) (residual : Thread E Bn) (σ' : Sg)
    (hseg : ThreadSegment handler R ts[i] σ xs residual σ') :
    interp_schedule_rr handler (n + 1) ts (some i) m σ ~
      emit_list (xs.map .inl) (interp_schedule_rr handler (n + 1) (ts.set i residual) none m σ') :=
  segment_interp_fair rr_scheduler handler R
    (fun X t u h => translate_sbisim relabel_log (HR X t u h)) n ts i m σ xs residual σ' hseg

end SegmentInterpretationRR

/-! ## Exact segments as guard/log token prefixes -/

section ExactPolicyPrefix
variable {E : Effect.{0}} {W Sg : Type} (sch : Scheduler)
  (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem exact_segment_fair_prefix (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (m : sch.sched_state) (σ : Sg) (logs : List W) (residual : Thread E Bn)
    (σ' : Sg) (h : ThreadSegment handler (fun _ t u => t = u) t σ logs residual σ') :
    ∃ word : List (RRToken (W ⊕ Nat)), rr_prefix_events word = logs.map .inl ∧
      interp_schedule_fair sch handler (n + 1) (ts.set i t) (some i) m σ =
        rr_prefix word
          (.guard (interp_schedule_fair sch handler (n + 1) (ts.set i residual) none m σ')) := by
  induction h with
  | yield k σ0 =>
    refine ⟨[], rfl, ?_⟩
    rw [interp_schedule_fair_yield_exact sch handler n _ i k m σ0 (by simp), Vector.set_set]
    rfl
  | @guard t0 _ _ _ _ _ ih =>
    obtain ⟨word, hw, ht⟩ := ih
    refine ⟨.guard :: word, hw, ?_⟩
    rw [interp_schedule_fair_guard_exact sch handler n _ i t0 m _ (by simp), Vector.set_set, ht]
    rfl
  | user e k σ0 result σ1 before after _ _ Eh _ ih =>
    obtain ⟨word, hw, ht⟩ := ih
    refine ⟨(before.map Sum.inl).map RRToken.log ++ .guard :: word, ?_, ?_⟩
    · rw [rr_prefix_events_app, rr_prefix_events_logs]
      simp [rr_prefix_events, hw]
    · have Eh : handler e σ0 = emit_list before (pure (result, σ1)) := Eh
      rw [exact_fair_user_replaced, Eh, translate_emit_list, translate_ret, emit_list_ret_bind]
      simp only [rr_guards, guards_succ, guards_zero]
      rw [ht, rr_prefix_app, rr_prefix_emit]
      rfl
  | equ htu _ hout ih => subst htu hout; exact ih

end ExactPolicyPrefix

section ExactRoundRobinPrefix
variable {E : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem exact_segment_rr_prefix (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (m : Nat) (σ : Sg) (logs : List W) (residual : Thread E Bn) (σ' : Sg)
    (h : ThreadSegment handler (fun _ t u => t = u) t σ logs residual σ') :
    ∃ word : List (RRToken (W ⊕ Nat)), rr_prefix_events word = logs.map .inl ∧
      interp_schedule_rr handler (n + 1) (ts.set i t) (some i) m σ =
        rr_prefix word
          (.guard (interp_schedule_rr handler (n + 1) (ts.set i residual) none m σ')) :=
  exact_segment_fair_prefix rr_scheduler handler n ts i t m σ logs residual σ' h

end ExactRoundRobinPrefix

/-! ## Closed turns

A focused first-yield segment that returns its slot to the same thread (up to finitely many
leading guards) leaves the same pool behind. -/

theorem closed_pool_guard_equ {E B : Effect.{0}} {n : Nat} (ts : Pool E B n) (i : Fin n)
    (residual : Thread E B) (htail : guard_equ residual ts[i]) :
    pool_guard_equ (ts.set i residual) ts := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using htail
  · rw [Fin.getElem_fin, Vector.getElem_set_ne _ _ (fun h => hj (Fin.ext h.symm))]
    exact .refl _

section SegmentPoolLoopND
variable {E B : Effect.{0}} [Bn -< B] {W Sg : Type}
  (handler : (e : E.I) → StateT Sg (ctreeW W B) (E.O e))

theorem segment_pool_nd_loop (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) (σ : Sg)
    (logs : List W) (σ' : Sg)
    (h : segment_to handler (fun _ t u => t = u) ts[i] σ logs ts[i] σ') :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      emit_list logs (interp_schedule_nd handler (n + 1) ts none σ') := by
  obtain ⟨residual, hseg, htail⟩ := h
  refine sbisim_trans (segment_interp_nd handler (fun _ t u => t ~ u) (fun _ _ _ h => h) n ts i
    σ logs residual σ' (ThreadSegment_mono handler _ _ (fun _ t u h => equ_sbisim t u h) _ _ _ _ _
      hseg)) ?_
  exact emit_list_sbisim _
    (interp_schedule_nd_guard_equ handler _ _ _ _ _ (closed_pool_guard_equ ts i residual htail))

end SegmentPoolLoopND

section SegmentPoolLoopPolicy
variable {E : Effect.{0}} {W Sg : Type} (sch : Scheduler)
  (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem segment_pool_fair_loop (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (st : sch.sched_state) (σ : Sg) (logs : List W) (σ' : Sg)
    (h : segment_to handler (fun _ t u => t = u) ts[i] σ logs ts[i] σ') :
    interp_schedule_fair sch handler (n + 1) ts (some i) st σ ~
      emit_list (logs.map .inl) (interp_schedule_fair sch handler (n + 1) ts none st σ') := by
  obtain ⟨residual, hseg, htail⟩ := h
  refine sbisim_trans (segment_interp_fair sch handler _
    (fun _ t u (h : t = u) => h ▸ sbisim_refl _) n ts i st σ logs residual σ' hseg) ?_
  exact emit_list_sbisim _ (interp_schedule_fair_guard_equ sch handler _ _ _ _ _ _
    (closed_pool_guard_equ ts i residual htail))

end SegmentPoolLoopPolicy

section SegmentPoolLoopRR
variable {E : Effect.{0}} {W Sg : Type} (handler : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem segment_pool_rr_loop (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (m : Nat)
    (σ : Sg) (logs : List W) (σ' : Sg)
    (h : segment_to handler (fun _ t u => t = u) ts[i] σ logs ts[i] σ') :
    interp_schedule_rr handler (n + 1) ts (some i) m σ ~
      emit_list (logs.map .inl) (interp_schedule_rr handler (n + 1) ts none m σ') :=
  segment_pool_fair_loop rr_scheduler handler n ts i m σ logs σ' h

end SegmentPoolLoopRR

-- Not ported: `unfold_spinS` (already `CTree.unfold_spinS`); `step_equ_node` (`congrArg`);
-- Ltac `vis_mismatch`/`head_absurd` (inlined as `simp [vis_eq_vis_iff']`); the section-local
-- `Abbreviation`s `Rexact`/`Rsb` (written inline as `fun _ t u => t = u` / `t ~ u`).

end Tisl.Yield
