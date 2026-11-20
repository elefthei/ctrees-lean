/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.SBisim
public import Logic.Interp.State
public import Logic.Yield.Policy
public import Logic.Yield.Nondeterministic

/-!
# Guard alignment of interpreters and schedulers

Pools up to finitely many leading guards (`pool_guard_equ`), and the guard-alignment results:
interpretation, state interpretation and the policy scheduler preserve `galigned`, each proved by
`galigned_coind` over an inductive proof relation; round-robin scheduling of branch-free pools is
branch-free (← `CTree/Interp/Yield/SBisim.v`, lines 1097-1139 and 1450-1897). Also holds
`interp_schedule_fair_guard_equ` (← `Policy.v`) and `interp_schedule_nd_guard_equ`
(← `Nondeterministic.v`), which need the alignment theorems.
-/

@[expose] public section
namespace Tisl.Yield
open CTree Lean.Order Coinduction
open ITree (Effect)

/-- Instrumented scheduling respects pointwise-equal pools. -/
theorem instr_schedule_pool_equ {Sg : Type} {B : Effect.{0}} [Bn -< B] (n : Nat)
    (v v' : Pool (stateE Sg) B n) (focus : Option (Fin n)) (σ : Sg) (hvv : pool_equ v v') :
    instr_schedule n v focus σ = instr_schedule n v' focus σ := by
  rw [Vector.ext fun i h => hvv ⟨i, h⟩]

/-! ## Pools up to finitely many leading guards -/

section PoolGuardEqu
variable {E B : Effect.{0}}

/-- The slotwise lift of `guard_equ`. -/
def pool_guard_equ {n : Nat} (ts us : Pool E B n) : Prop := ∀ i : Fin n, guard_equ ts[i] us[i]

theorem pool_equ_guard {n} (ts us : Pool E B n) (h : pool_equ ts us) : pool_guard_equ ts us :=
  fun i => guard_equ_equ _ _ (h i)

theorem pool_replace_current {n} (ts : Pool E B n) (i : Fin n) : pool_equ (ts.set i ts[i]) ts :=
  fun j => by simp

theorem pool_equ_guard_trans {n} (ts us vs : Pool E B n) (heq : pool_equ ts us)
    (h : pool_guard_equ us vs) : pool_guard_equ ts vs :=
  fun i => guard_equ_trans _ _ _ (guard_equ_equ _ _ (heq i)) (h i)

theorem pool_guard_equ_replace {N} (ts us : Pool E B N) (i : Fin N) (x : Thread E B)
    (hp : pool_guard_equ ts us) : pool_guard_equ (ts.set i x) (us.set i x) :=
  vector_replace_pointwise (fun a b : Thread E B => guard_equ a b) ts us i x x
    (fun j _ => hp j) (.refl x)

theorem pool_guard_equ_remove {N} (ts us : Pool E B (N + 1)) (i : Fin (N + 1))
    (hp : pool_guard_equ ts us) : pool_guard_equ (ts.eraseIdx i) (us.eraseIdx i) :=
  vector_remove_pointwise (fun a b : Thread E B => guard_equ a b) ts us i fun j _ => hp j

theorem pool_guard_equ_cons {N} (x : Thread E B) (ts us : Pool E B N)
    (hp : pool_guard_equ ts us) : pool_guard_equ (Vector.cons x ts) (Vector.cons x us) :=
  vector_cons_pointwise (fun a b : Thread E B => guard_equ a b) x x ts us (.refl x) hp

end PoolGuardEqu

/-! ## Interpretation preserves guard alignment -/

section InterpAlign
variable {E F B : Effect.{u}} (h : (e : E.I) → CTree F B (E.O e)) {X : Type u}

theorem interp_guards (n : Nat) (t : CTree E B X) :
    interp h (guards n t) = guards n (interp h t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [guards_succ, interp_guard, ih]

/-- Proof relation for `interp_galigned` (Rocq `interp_rel`): interpreted aligned trees, or an
interpreted handler answer bound to aligned continuations, each behind finitely many guards. -/
inductive InterpRel : Rel (CTree F B X) (CTree F B X)
  | tree (n m : Nat) (t u : CTree E B X) {T U : CTree F B X} :
      galigned t u → T = guards n (interp h t) → U = guards m (interp h u) → InterpRel T U
  | bind (n m : Nat) {A : Type u} (a : CTree F B A) (k k' : A → CTree E B X)
      {T U : CTree F B X} : (∀ x, galigned (k x) (k' x)) →
      T = guards n (a >>= fun x => .guard (interp h (k x))) →
      U = guards m (a >>= fun x => .guard (interp h (k' x))) → InterpRel T U

theorem interp_rel_bind_step (n m : Nat) {A : Type u} (a : CTree F B A)
    (k k' : A → CTree E B X) {T U : CTree F B X} (hk : ∀ x, galigned (k x) (k' x))
    (hT : T = guards n (a >>= fun x => .guard (interp h (k x))))
    (hU : U = guards m (a >>= fun x => .guard (interp h (k' x)))) :
    GalignF (InterpRel h) T U := by
  subst hT hU
  cases a with
  | ret x =>
    exact .guard n m (interp h (k x)) (interp h (k' x)) (by rw [pure_bind', guards_guard])
      (by rw [pure_bind', guards_guard]) (.tree 0 0 _ _ (hk x) rfl rfl)
  | stuck => exact .stuck n m (by rw [stuck_bind]) (by rw [stuck_bind])
  | step s =>
    exact .step n m _ _ (by rw [step_bind]; rfl) (by rw [step_bind]; rfl)
      (.bind 0 0 s k k' hk rfl rfl)
  | guard g =>
    exact .guard n m _ _ (by rw [guard_bind, guards_guard]; rfl)
      (by rw [guard_bind, guards_guard]; rfl)
      (.bind 0 0 g k k' hk rfl rfl)
  | vis e kk =>
    exact .vis n m e _ _ (by rw [vis_bind]; rfl) (by rw [vis_bind]; rfl)
      fun y => .bind 0 0 (kk y) k k' hk rfl rfl
  | br c kk =>
    exact .br n m c _ _ (by rw [br_bind]; rfl) (by rw [br_bind]; rfl)
      fun i => .bind 0 0 (kk i) k k' hk rfl rfl

theorem interp_rel_step (T U : CTree F B X) (hr : InterpRel h T U) :
    GalignF (InterpRel h) T U := by
  match hr with
  | .bind n m a k k' hk hT hU => exact interp_rel_bind_step h n m a k k' hk hT hU
  | .tree n m t u ha hT hU =>
    subst hT hU
    match galigned_unfold.1 ha with
    | .guard a b t' u' ht hu ha' =>
      subst ht hu
      exact .guard (n + a) (m + b) (interp h t') (interp h u')
        (by rw [interp_guards, guards_shift]) (by rw [interp_guards, guards_shift])
        (.tree 0 0 t' u' ha' rfl rfl)
    | .ret a b r ht hu =>
      subst ht hu
      exact .ret (n + a) (m + b) r
        (by rw [interp_guards, guards_add]; exact congrArg (guards n ∘ guards a) (interp_ret h r))
        (by rw [interp_guards, guards_add]; exact congrArg (guards m ∘ guards b) (interp_ret h r))
    | .br a b c kk kk' ht hu hk =>
      subst ht hu
      exact .br (n + a) (m + b) c (fun i => .guard (interp h (kk i)))
        (fun i => .guard (interp h (kk' i))) (by rw [interp_guards, interp_br', guards_add]; rfl)
        (by rw [interp_guards, interp_br', guards_add]; rfl) fun i => .tree 1 1 _ _ (hk i) rfl rfl
    | .vis a b e kk kk' ht hu hk =>
      subst ht hu
      exact interp_rel_bind_step h (n + a) (m + b) (h e) kk kk' hk
        (by rw [interp_guards, interp_vis, guards_add])
        (by rw [interp_guards, interp_vis, guards_add])
    | .stuck a b ht hu =>
      subst ht hu
      exact .stuck (n + a) (m + b) (by rw [interp_guards, interp_stuck, guards_add])
        (by rw [interp_guards, interp_stuck, guards_add])
    | .step a b t' u' ht hu ha' =>
      subst ht hu
      exact .step (n + a) (m + b) (.guard (interp h t')) (.guard (interp h u'))
        (by rw [interp_guards, interp_step, guards_add])
        (by rw [interp_guards, interp_step, guards_add])
        (.tree 1 1 t' u' ha' rfl rfl)

/-- Interpreting aligned trees preserves alignment. -/
theorem interp_galigned (t u : CTree E B X) (ha : galigned t u) :
    galigned (interp h t) (interp h u) :=
  galigned_coind (InterpRel h) (interp_rel_step h) _ _ (.tree 0 0 t u ha rfl rfl)

end InterpAlign

/-! ## State interpretation preserves guard alignment -/

section InterpStateAlign
variable {E F B : Effect.{u}} {S : Type u} (h : (e : E.I) → StateT S (CTree F B) (E.O e))
  {X : Type u}

theorem interp_state_guards (n : Nat) (t : CTree E B X) (s : S) :
    interp_state h (guards n t) s = guards n (interp_state h t s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [guards_succ, interp_state_guard, ih]

theorem interp_state_br_node (c : B.I) (k : B.O c → CTree E B X) (s : S) :
    interp_state h (.br c k) s = .br c fun y => .guard (interp_state h (k y) s) := by
  simp only [interp_state_br, CTree.branch', CTree.br', br_bind, pure_bind']
  rfl

/-- Proof relation for `interp_state_galigned` (Rocq `istate_rel`). -/
inductive IstateRel : Rel (CTree F B (X × S)) (CTree F B (X × S))
  | tree (n m : Nat) (t u : CTree E B X) (s : S) {T U : CTree F B (X × S)} :
      galigned t u → T = guards n (interp_state h t s) → U = guards m (interp_state h u s) →
      IstateRel T U
  | bind (n m : Nat) {A : Type u} (a : CTree F B (A × S)) (k k' : A → CTree E B X)
      {T U : CTree F B (X × S)} : (∀ x, galigned (k x) (k' x)) →
      T = guards n (a >>= fun sx => .guard (interp_state h (k sx.1) sx.2)) →
      U = guards m (a >>= fun sx => .guard (interp_state h (k' sx.1) sx.2)) → IstateRel T U

theorem istate_rel_bind_step (n m : Nat) {A : Type u} (a : CTree F B (A × S))
    (k k' : A → CTree E B X) {T U : CTree F B (X × S)} (hk : ∀ x, galigned (k x) (k' x))
    (hT : T = guards n (a >>= fun sx => .guard (interp_state h (k sx.1) sx.2)))
    (hU : U = guards m (a >>= fun sx => .guard (interp_state h (k' sx.1) sx.2))) :
    GalignF (IstateRel h) T U := by
  subst hT hU
  cases a with
  | ret xs =>
    obtain ⟨x, s'⟩ := xs
    exact .guard n m (interp_state h (k x) s') (interp_state h (k' x) s')
      (by rw [pure_bind', guards_guard]) (by rw [pure_bind', guards_guard])
      (.tree 0 0 _ _ s' (hk x) rfl rfl)
  | stuck => exact .stuck n m (by rw [stuck_bind]) (by rw [stuck_bind])
  | step st =>
    exact .step n m _ _ (by rw [step_bind]; rfl) (by rw [step_bind]; rfl)
      (.bind 0 0 st k k' hk rfl rfl)
  | guard g =>
    exact .guard n m _ _ (by rw [guard_bind, guards_guard]; rfl)
      (by rw [guard_bind, guards_guard]; rfl)
      (.bind 0 0 g k k' hk rfl rfl)
  | vis e kk =>
    exact .vis n m e _ _ (by rw [vis_bind]; rfl) (by rw [vis_bind]; rfl)
      fun y => .bind 0 0 (kk y) k k' hk rfl rfl
  | br c kk =>
    exact .br n m c _ _ (by rw [br_bind]; rfl) (by rw [br_bind]; rfl)
      fun i => .bind 0 0 (kk i) k k' hk rfl rfl

theorem istate_rel_step (T U : CTree F B (X × S)) (hr : IstateRel h T U) :
    GalignF (IstateRel h) T U := by
  match hr with
  | .bind n m a k k' hk hT hU => exact istate_rel_bind_step h n m a k k' hk hT hU
  | .tree n m t u s ha hT hU =>
    subst hT hU
    match galigned_unfold.1 ha with
    | .guard a b t' u' ht hu ha' =>
      subst ht hu
      exact .guard (n + a) (m + b) (interp_state h t' s) (interp_state h u' s)
        (by rw [interp_state_guards, guards_shift]) (by rw [interp_state_guards, guards_shift])
        (.tree 0 0 t' u' s ha' rfl rfl)
    | .ret a b r ht hu =>
      subst ht hu
      exact .ret (n + a) (m + b) (r, s)
        (by rw [interp_state_guards, guards_add]
            exact congrArg (guards n ∘ guards a) (interp_state_ret h r s))
        (by rw [interp_state_guards, guards_add]
            exact congrArg (guards m ∘ guards b) (interp_state_ret h r s))
    | .br a b c kk kk' ht hu hk =>
      subst ht hu
      exact .br (n + a) (m + b) c (fun i => .guard (interp_state h (kk i) s))
        (fun i => .guard (interp_state h (kk' i) s))
        (by rw [interp_state_guards, interp_state_br_node, guards_add])
        (by rw [interp_state_guards, interp_state_br_node, guards_add])
        fun i => .tree 1 1 _ _ s (hk i) rfl rfl
    | .vis a b e kk kk' ht hu hk =>
      subst ht hu
      exact istate_rel_bind_step h (n + a) (m + b) (h e s) kk kk' hk
        (by rw [interp_state_guards, interp_state_vis, guards_add])
        (by rw [interp_state_guards, interp_state_vis, guards_add])
    | .stuck a b ht hu =>
      subst ht hu
      exact .stuck (n + a) (m + b) (by rw [interp_state_guards, interp_state_stuck, guards_add])
        (by rw [interp_state_guards, interp_state_stuck, guards_add])
    | .step a b t' u' ht hu ha' =>
      subst ht hu
      exact .step (n + a) (m + b) (.guard (interp_state h t' s)) (.guard (interp_state h u' s))
        (by rw [interp_state_guards, interp_state_step, guards_add])
        (by rw [interp_state_guards, interp_state_step, guards_add])
        (.tree 1 1 t' u' s ha' rfl rfl)

/-- State interpretation of aligned trees from the same state preserves alignment. -/
theorem interp_state_galigned (t u : CTree E B X) (s : S) (ha : galigned t u) :
    galigned (interp_state h t s) (interp_state h u s) :=
  galigned_coind (IstateRel h) (istate_rel_step h) _ _ (.tree 0 0 t u s ha rfl rfl)

end InterpStateAlign

/-! ## The policy scheduler preserves guard alignment -/

section ScheduleAlign
variable {E B : Effect.{0}} [Bn -< B] (sch : Scheduler)

theorem schedule_policy_focus_guards (st : sch.sched_state) (a : Nat) : ∀ (N : Nat)
    (ts : Pool E B (N + 1)) (i : Fin (N + 1)) (x : Thread E B), ts[i] = guards a x →
    schedule_policy sch (N + 1) ts (some i) st =
      guards a (schedule_policy sch (N + 1) (ts.set i x) (some i) st) := by
  induction a with
  | zero =>
    intro N ts i x hx
    subst hx
    exact (schedule_policy_pool_proper sch _ _ _ _ _ (pool_replace_current ts i)).symm
  | succ a ih =>
    intro N ts i x hx
    rw [schedule_policy_focused_guard_equ sch N ts i (guards a x) st
        (by rw [hx, guards_succ, unfold_guard]),
      ih N (ts.set i (guards a x)) i x (by simp)]
    simp

/-- Proof relation for `schedule_policy_galigned` (Rocq `sched_rel`): guard-equivalent pools at a
scheduler root (`node`, Rocq `sched_rel_at`), at a hidden selection branch (`choice`), or after
the selection event (`selected`), each behind finitely many guards. -/
inductive SchedRel : Rel (Completed E B) (Completed E B)
  | node (n m N : Nat) (ts us : Pool E B N) (f : Option (Fin N)) (st : sch.sched_state)
      {T U : Completed E B} : pool_guard_equ ts us →
      T = guards n (schedule_policy sch N ts f st) →
      U = guards m (schedule_policy sch N us f st) → SchedRel T U
  | choice (n m N a : Nat) (ts us : Pool E B (N + 1))
      (pick : Fin (a + 2) → Fin (N + 1) × sch.sched_state) {T U : Completed E B} :
      pool_guard_equ ts us →
      T = (guards n (CTree.brn (a + 2) fun x => .vis (.inr (slot_index (pick x).1))
        fun _ => schedule_policy sch (N + 1) ts (some (pick x).1) (pick x).2) : Completed E B) →
      U = (guards m (CTree.brn (a + 2) fun x => .vis (.inr (slot_index (pick x).1))
        fun _ => schedule_policy sch (N + 1) us (some (pick x).1) (pick x).2) : Completed E B) →
      SchedRel T U
  | selected (n m N : Nat) (ts us : Pool E B (N + 1)) (i : Fin (N + 1)) (st : sch.sched_state)
      {T U : Completed E B} : pool_guard_equ ts us →
      T = (guards n (.vis (.inr (slot_index i)) fun _ =>
        schedule_policy sch (N + 1) ts (some i) st) : Completed E B) →
      U = (guards m (.vis (.inr (slot_index i)) fun _ =>
        schedule_policy sch (N + 1) us (some i) st) : Completed E B) →
      SchedRel T U

/-- An unfocused selection over `ar + 1` alternatives aligns. -/
private theorem sched_rel_select (n m N ar : Nat) (ts us : Pool E B (N + 1))
    (pick : Fin (ar + 1) → Fin (N + 1) × sch.sched_state) (hp : pool_guard_equ ts us)
    {T U : Completed E B}
    (hT : T = (guards n (br_alts ar fun x => .vis (.inr (slot_index (pick x).1))
      fun _ => schedule_policy sch (N + 1) ts (some (pick x).1) (pick x).2) : Completed E B))
    (hU : U = (guards m (br_alts ar fun x => .vis (.inr (slot_index (pick x).1))
      fun _ => schedule_policy sch (N + 1) us (some (pick x).1) (pick x).2) : Completed E B)) :
    GalignF (SchedRel sch) T U := by
  cases ar with
  | zero =>
    exact .vis n m _ _ _ hT hU fun _ => .node 0 0 (N + 1) ts us _ _ hp rfl rfl
  | succ a =>
    exact .br n m _ _ _ hT hU fun _ => .selected 0 0 N ts us _ _ hp rfl rfl

theorem sched_rel_step (T U : Completed E B) (hr : SchedRel sch T U) :
    GalignF (SchedRel sch) T U := by
  match hr with
  | .choice n m N a ts us pick hp hT hU =>
    exact .br n m _ _ _ hT hU fun _ => .selected 0 0 N ts us _ _ hp rfl rfl
  | .selected n m N ts us i st hp hT hU =>
    exact .vis n m _ _ _ hT hU fun _ => .node 0 0 (N + 1) ts us (some i) st hp rfl rfl
  | .node n m 0 ts us none st hp hT hU =>
    exact .ret n m ⟨⟩ (by rw [hT, schedule_policy_empty_equ])
      (by rw [hU, schedule_policy_empty_equ])
  | .node n m (N + 1) ts us none st hp hT hU =>
    rw [schedule_policy_no_focus_equ] at hT hU
    exact sched_rel_select sch n m N _ ts us (sch.sched_pick N st) hp hT hU
  | .node n m 0 ts us (some i) st hp hT hU => exact i.elim0
  | .node n m (N + 1) ts us (some i) st hp hT hU =>
    obtain ⟨a, b, x, Ea, Eb⟩ := guard_equ_guards _ _ (hp i)
    have hp' := pool_guard_equ_replace ts us i x hp
    have ET : T = guards (n + a) (schedule_policy sch (N + 1) (ts.set i x) (some i) st) := by
      rw [hT, schedule_policy_focus_guards sch st a N ts i x Ea, guards_add]
    have EU : U = guards (m + b) (schedule_policy sch (N + 1) (us.set i x) (some i) st) := by
      rw [hU, schedule_policy_focus_guards sch st b N us i x Eb, guards_add]
    have Hts : (ts.set i x)[i].unfold = x.unfold := by simp
    have Hus : (us.set i x)[i].unfold = x.unfold := by simp
    generalize ts.set i x = ts' at ET hp' Hts
    generalize us.set i x = us' at EU hp' Hus
    clear hT hU
    cases hx : x.unfold with
    | ret r =>
      rw [hx] at Hts Hus
      exact .guard (n + a) (m + b) (schedule_policy sch N (ts'.eraseIdx i) none st)
        (schedule_policy sch N (us'.eraseIdx i) none st)
        (by rw [ET, schedule_policy_focused_ret_equ sch N ts' i st Hts, guards_guard])
        (by rw [EU, schedule_policy_focused_ret_equ sch N us' i st Hus, guards_guard])
        (.node 0 0 N _ _ none st (pool_guard_equ_remove ts' us' i hp') rfl rfl)
    | stuck =>
      rw [hx] at Hts Hus
      exact .stuck (n + a) (m + b)
        (by rw [ET, schedule_policy_focused_stuck_equ sch N ts' i st Hts])
        (by rw [EU, schedule_policy_focused_stuck_equ sch N us' i st Hus])
    | step t =>
      rw [hx] at Hts Hus
      exact .step (n + a) (m + b) (schedule_policy sch (N + 1) (ts'.set i t) (some i) st)
        (schedule_policy sch (N + 1) (us'.set i t) (some i) st)
        (by rw [ET, schedule_policy_focused_step_equ sch N ts' i t st Hts])
        (by rw [EU, schedule_policy_focused_step_equ sch N us' i t st Hus])
        (.node 0 0 (N + 1) _ _ (some i) st (pool_guard_equ_replace _ _ i t hp') rfl rfl)
    | guard t =>
      rw [hx] at Hts Hus
      exact .guard (n + a) (m + b) (schedule_policy sch (N + 1) (ts'.set i t) (some i) st)
        (schedule_policy sch (N + 1) (us'.set i t) (some i) st)
        (by rw [ET, schedule_policy_focused_guard_equ sch N ts' i t st Hts, guards_guard])
        (by rw [EU, schedule_policy_focused_guard_equ sch N us' i t st Hus, guards_guard])
        (.node 0 0 (N + 1) _ _ (some i) st (pool_guard_equ_replace _ _ i t hp') rfl rfl)
    | vis e k =>
      rw [hx] at Hts Hus
      rcases e with ⟨⟩ | ⟨⟩ | e
      · exact .guard (n + a) (m + b) (schedule_policy sch (N + 1) (ts'.set i (k ⟨⟩)) none st)
          (schedule_policy sch (N + 1) (us'.set i (k ⟨⟩)) none st)
          (by rw [ET, schedule_policy_focused_yield_equ sch N ts' i k st Hts, guards_guard])
          (by rw [EU, schedule_policy_focused_yield_equ sch N us' i k st Hus, guards_guard])
          (.node 0 0 (N + 1) _ _ none st (pool_guard_equ_replace _ _ i _ hp') rfl rfl)
      · exact .guard (n + a) (m + b)
          (schedule_policy sch (N + 2) (Vector.cons (k true) (ts'.set i (k false)))
            (some i.succ) st)
          (schedule_policy sch (N + 2) (Vector.cons (k true) (us'.set i (k false)))
            (some i.succ) st)
          (by rw [ET, schedule_policy_focused_fork_equ sch N ts' i k st Hts, guards_guard])
          (by rw [EU, schedule_policy_focused_fork_equ sch N us' i k st Hus, guards_guard])
          (.node 0 0 (N + 2) _ _ (some i.succ) st
            (pool_guard_equ_cons _ _ _ (pool_guard_equ_replace _ _ i _ hp')) rfl rfl)
      · exact .vis (n + a) (m + b) (.inl e)
          (fun z => schedule_policy sch (N + 1) (ts'.set i (k z)) (some i) st)
          (fun z => schedule_policy sch (N + 1) (us'.set i (k z)) (some i) st)
          (by rw [ET, schedule_policy_focused_user_event_equ sch N ts' i e k st Hts])
          (by rw [EU, schedule_policy_focused_user_event_equ sch N us' i e k st Hus])
          fun z => .node 0 0 (N + 1) _ _ (some i) st (pool_guard_equ_replace _ _ i _ hp') rfl rfl
    | br c k =>
      rw [hx] at Hts Hus
      exact .br (n + a) (m + b) c
        (fun j => schedule_policy sch (N + 1) (ts'.set i (k j)) (some i) st)
        (fun j => schedule_policy sch (N + 1) (us'.set i (k j)) (some i) st)
        (by rw [ET, schedule_policy_focused_br_equ sch N ts' i k st Hts])
        (by rw [EU, schedule_policy_focused_br_equ sch N us' i k st Hus])
        fun j => .node 0 0 (N + 1) _ _ (some i) st (pool_guard_equ_replace _ _ i _ hp') rfl rfl

/-- The policy scheduler aligns guard-equivalent pools. -/
theorem schedule_policy_galigned (N : Nat) (ts us : Pool E B N) (f : Option (Fin N))
    (st : sch.sched_state) (hp : pool_guard_equ ts us) :
    galigned (schedule_policy sch N ts f st) (schedule_policy sch N us f st) :=
  galigned_coind (SchedRel sch) (sched_rel_step sch) _ _ (.node 0 0 N ts us f st hp rfl rfl)

/-- …also after projecting the selection events to silent steps. -/
theorem erased_schedule_policy_galigned (N : Nat) (ts us : Pool E B N) (f : Option (Fin N))
    (st : sch.sched_state) (hp : pool_guard_equ ts us) :
    galigned (project_scheduled (schedule_policy sch N ts f st))
      (project_scheduled (schedule_policy sch N us f st)) :=
  interp_galigned _ _ _ (schedule_policy_galigned sch N ts us f st hp)

end ScheduleAlign

/-! ## Nondeterministic and round-robin specializations -/

section ScheduleAlignmentSpecializations
variable {E B : Effect.{0}} [Bn -< B]

theorem schedule_focus_guards (a N : Nat) (ts : Pool E B (N + 1)) (i : Fin (N + 1))
    (x : Thread E B) (hx : ts[i] = guards a x) :
    schedule (N + 1) ts (some i) = guards a (schedule (N + 1) (ts.set i x) (some i)) :=
  schedule_policy_focus_guards nd_scheduler ⟨⟩ a N ts i x hx

theorem schedule_galigned (N : Nat) (ts us : Pool E B N) (f : Option (Fin N))
    (hp : pool_guard_equ ts us) : galigned (schedule N ts f) (schedule N us f) :=
  schedule_policy_galigned nd_scheduler N ts us f ⟨⟩ hp

theorem schedule_rr_galigned (N : Nat) (ts us : Pool E B N) (f : Option (Fin N)) (cursor : Nat)
    (hp : pool_guard_equ ts us) :
    galigned (schedule_rr N ts f cursor) (schedule_rr N us f cursor) :=
  schedule_policy_galigned rr_scheduler N ts us f cursor hp

theorem erased_schedule_galigned (N : Nat) (ts us : Pool E B N) (f : Option (Fin N))
    (hp : pool_guard_equ ts us) :
    galigned (project_scheduled (schedule N ts f)) (project_scheduled (schedule N us f)) :=
  erased_schedule_policy_galigned nd_scheduler N ts us f ⟨⟩ hp

theorem erased_schedule_rr_galigned (N : Nat) (ts us : Pool E B N) (f : Option (Fin N))
    (cursor : Nat) (hp : pool_guard_equ ts us) :
    galigned (project_scheduled (schedule_rr N ts f cursor))
      (project_scheduled (schedule_rr N us f cursor)) :=
  erased_schedule_policy_galigned rr_scheduler N ts us f cursor hp

end ScheduleAlignmentSpecializations

/-- Round-robin introduces no branch, including at a singleton boundary. -/
theorem branchfree_schedule_rr {E B : Effect.{0}} [Bn -< B] (n : Nat) (ts : Pool E B n)
    (focus : Option (Fin n)) (cursor : Nat) (hbf : pool_branchfree ts) :
    BranchFree (schedule_rr n ts focus cursor) := by
  refine branchfree_invariant (fun t => ∃ (n : Nat) (ts : Pool E B n) (focus : Option (Fin n))
    (cursor : Nat),
    pool_branchfree ts ∧ t = schedule_rr n ts focus cursor) ?_ _ ⟨n, ts, focus, cursor, hbf, rfl⟩
  rintro _ ⟨n, ts, focus, cursor, hbf, rfl⟩
  match n, ts, focus, hbf with
  | 0, ts, none, _ => rw [schedule_rr_empty_none]; exact .ret _
  | n + 1, ts, none, hbf =>
    rw [schedule_rr_no_focus_nonempty]
    exact .vis _ _ fun _ => ⟨n + 1, ts, some _, _, hbf, rfl⟩
  | 0, _, some i, _ => exact i.elim0
  | n + 1, ts, some i, hbf =>
    have Hi := (branchfree_unfold _).1 (hbf i)
    generalize hobs : ts[i].unfold = o at Hi
    cases Hi with
    | ret r =>
      rw [schedule_rr_focused_ret n ts i cursor hobs]
      exact .guard _ ⟨n, _, none, cursor, pool_branchfree_remove ts i hbf, rfl⟩
    | stuck => rw [schedule_rr_focused_stuck n ts i cursor hobs]; exact .stuck
    | step t ht =>
      rw [schedule_rr_focused_step n ts i t cursor hobs]
      exact .step _ ⟨n + 1, _, some i, cursor, pool_branchfree_replace ts i t hbf ht, rfl⟩
    | guard t ht =>
      rw [schedule_rr_focused_guard n ts i t cursor hobs]
      exact .guard _ ⟨n + 1, _, some i, cursor, pool_branchfree_replace ts i t hbf ht, rfl⟩
    | vis e k hk =>
      rcases e with ⟨⟩ | ⟨⟩ | e
      · rw [schedule_rr_focused_yield n ts i k cursor hobs]
        exact .guard _ ⟨n + 1, _, none, cursor, pool_branchfree_replace ts i _ hbf (hk ⟨⟩), rfl⟩
      · rw [schedule_rr_focused_fork n ts i k cursor hobs]
        exact .guard _ ⟨n + 2, _, some i.succ, cursor,
          pool_branchfree_cons _ _ (hk true) (pool_branchfree_replace ts i _ hbf (hk false)), rfl⟩
      · rw [schedule_rr_focused_user_event n ts i e k cursor hobs]
        exact .vis _ _ fun z => ⟨n + 1, _, some i, cursor,
          pool_branchfree_replace ts i _ hbf (hk z), rfl⟩

/-! ## Guard-equivalent pools under the instrumented runners (moved from `Policy.v` and
`Nondeterministic.v`) -/

/-- Guard-equivalent pools are bisimilar under the policy runner. -/
theorem interp_schedule_fair_guard_equ {E : Effect.{0}} {W Sg : Type} (sch : Scheduler)
    (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) (n : Nat) (ts us : Pool E Bn n)
    (focus : Option (Fin n)) (st : sch.sched_state) (σ : Sg) (hp : pool_guard_equ ts us) :
    interp_schedule_fair sch h n ts focus st σ ~ interp_schedule_fair sch h n us focus st σ :=
  galigned_sbisim _ _
    (interp_state_galigned _ _ _ σ (schedule_policy_galigned sch n ts us focus st hp))

/-- Guard-equivalent pools are bisimilar under nondeterministic scheduling, for every focus and
state. -/
theorem interp_schedule_nd_guard_equ {E F B : Effect.{0}} [Bn -< B] {Sg : Type}
    (handler : (e : E.I) → StateT Sg (CTree F B) (E.O e)) (n : Nat) (ts us : Pool E B n)
    (focus : Option (Fin n)) (σ : Sg) (hp : pool_guard_equ ts us) :
    interp_schedule_nd handler n ts focus σ ~ interp_schedule_nd handler n us focus σ :=
  galigned_sbisim _ _ (interp_state_galigned _ _ _ σ (erased_schedule_galigned n ts us focus hp))

end Tisl.Yield

-- Not ported: none dropped. Rocq's `schedule_policy_pool_proper` rewrite in
-- `instr_schedule_pool_equ` is `Vector.ext`; `observe_equ_go` node equations are the shared
-- `schedule_policy_*_equ` of `Logic/Yield/SBisim.lean`.
