/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Mod
public import Logic.Interp.Refine
public import Logic.Interp.State
public import Logic.CTree.Core
public import Logic.Utils.Vectors

/-!
# Guard equivalence, bisimilar pools and guard alignment

Foundation of the scheduler congruence results: equivalence up to finitely many leading guards
(`guard_equ`), pointwise bisimilar / equal / branch-free pools, and the coinductive guard alignment
`galigned`, which implies strong bisimulation (← `CTree/Interp/Yield/SBisim.v`, lines 1-219 and
1140-1448; the scheduler theorems live in `Logic/Yield/SBisimSchedule.lean`).
-/

@[expose] public section
namespace Tisl
open CTree Lean.Order Coinduction
open ITree (Effect)

/-- Reflexive, symmetric, transitive closure (Rocq `clos_refl_sym_trans`). -/
inductive EqvGen {α : Sort _} (r : α → α → Prop) : α → α → Prop
  | rel {x y} : r x y → EqvGen r x y
  | refl x : EqvGen r x x
  | symm {x y} : EqvGen r x y → EqvGen r y x
  | trans {x y z} : EqvGen r x y → EqvGen r y z → EqvGen r x z

namespace Yield

section GuardEqu
variable {E B : Effect.{u}} {X : Type u}

/-- Equal observations give equal trees. -/
theorem observe_eq_equ (t u : CTree E B X) (h : t.unfold = u.unfold) : t = u := unfold_inj h

theorem observe_equ_go (t : CTree E B X) (ot : CTreeF E B X (CTree E B X)) (h : t.unfold = ot) :
    t = CTree.fold ot := by
  subst h; exact (fold_unfold t).symm

/-- Equal, or one leading guard away. -/
def guard_step (t u : CTree E B X) : Prop := t = u ∨ t = .guard u

/-- Equivalence closure of `guard_step`: forgets only finitely many leading guards. -/
def guard_equ : CTree E B X → CTree E B X → Prop := EqvGen guard_step

theorem guard_equ_equ (t u : CTree E B X) (h : t = u) : guard_equ t u := .rel (.inl h)

theorem guard_equ_left (t u : CTree E B X) (h : guard_equ t u) : guard_equ (.guard t) u :=
  .trans (.rel (.inr rfl)) h

theorem guard_equ_right (t u : CTree E B X) (h : guard_equ t u) : guard_equ t (.guard u) :=
  .trans h (.symm (.rel (.inr rfl)))

theorem guard_equ_sym (t u : CTree E B X) (h : guard_equ t u) : guard_equ u t := .symm h

theorem guard_equ_trans (t u v : CTree E B X) (h₁ : guard_equ t u) (h₂ : guard_equ u v) :
    guard_equ t v := .trans h₁ h₂

/-- Forgetting finitely many leading guards is a strong bisimulation. -/
theorem guard_equ_sbisim (t u : CTree E B X) (h : guard_equ t u) : t ~ u := by
  induction h with
  | rel h => rcases h with rfl | rfl
             · exact sbisim_refl _
             · exact sb_guard _
  | refl => exact sbisim_refl _
  | symm _ ih => exact sbisim_symm ih
  | trans _ _ ih₁ ih₂ => exact sbisim_trans ih₁ ih₂

theorem guard_equ_Equivalence : Equivalence (guard_equ (E := E) (B := B) (X := X)) :=
  ⟨.refl, .symm, .trans⟩

end GuardEqu

/-- One transition of a `~` pair, played from the left. -/
theorem sbisim_trans_l {E B : Effect.{u}} {X : Type u} (t u t' : CTree E B X) (l : Label E)
    (h : t ~ u) (tr : trans l t t') : ∃ u', trans l u u' ∧ t' ~ u' := by
  obtain ⟨_, u', tr', h', rfl⟩ := (sbisim_unfold.1 h).1 l t' tr
  exact ⟨u', tr', h'⟩

/-- Transitions preserve branch freedom. -/
theorem branchfree_trans {E B : Effect.{u}} {X : Type u} (t u : CTree E B X) (l : Label E)
    (hb : BranchFree t) (tr : CTree.trans l t u) : BranchFree u := by
  unfold CTree.trans at tr
  generalize ht : t.unfold = T at tr
  induction tr generalizing t with
  | br => rw [branchfree_unfold, ht] at hb; cases hb
  | guard _ ih =>
    rw [branchfree_unfold, ht] at hb
    cases hb with | guard _ h => exact ih _ h rfl
  | step => rw [branchfree_unfold, ht] at hb; cases hb with | step _ h => exact h
  | obs x => rw [branchfree_unfold, ht] at hb; cases hb with | vis _ _ h => exact h x
  | val => exact bf_stuck

section PoolSBisim
variable {E B : Effect.{0}}

/-- Pointwise bisimilar pools. -/
def pool_sbisim {n : Nat} (v1 v2 : Pool E B n) : Prop := ∀ i : Fin n, v1[i] ~ v2[i]

theorem pool_sbisim_sym {n} (v1 v2 : Pool E B n) (h : pool_sbisim v1 v2) : pool_sbisim v2 v1 :=
  fun i => sbisim_symm (h i)

theorem replace_pool_sbisim {n} (v1 v2 : Pool E B n) (i : Fin n) (t1 t2 : Thread E B)
    (hv : pool_sbisim v1 v2) (ht : t1 ~ t2) : pool_sbisim (v1.set i t1) (v2.set i t2) :=
  vector_replace_pointwise (fun a b : Thread E B => a ~ b) v1 v2 i t1 t2 (fun j _ => hv j) ht

theorem remove_pool_sbisim {n} (v1 v2 : Pool E B (n + 1)) (i : Fin (n + 1))
    (hv : pool_sbisim v1 v2) : pool_sbisim (v1.eraseIdx i) (v2.eraseIdx i) :=
  vector_remove_pointwise (fun a b : Thread E B => a ~ b) v1 v2 i (fun j _ => hv j)

theorem cons_pool_sbisim {n} (t1 t2 : Thread E B) (v1 v2 : Pool E B n) (ht : t1 ~ t2)
    (hv : pool_sbisim v1 v2) : pool_sbisim (Vector.cons t1 v1) (Vector.cons t2 v2) :=
  vector_cons_pointwise (fun a b : Thread E B => a ~ b) t1 t2 v1 v2 ht hv

/-- Pointwise equal pools. -/
def pool_equ {n : Nat} (v1 v2 : Pool E B n) : Prop := ∀ i : Fin n, v1[i] = v2[i]

theorem replace_pool_equ {n} (v1 v2 : Pool E B n) (i : Fin n) (t1 t2 : Thread E B)
    (hv : pool_equ v1 v2) (ht : t1 = t2) : pool_equ (v1.set i t1) (v2.set i t2) :=
  vector_replace_pointwise (fun a b : Thread E B => a = b) v1 v2 i t1 t2 (fun j _ => hv j) ht

theorem remove_pool_equ {n} (v1 v2 : Pool E B (n + 1)) (i : Fin (n + 1)) (hv : pool_equ v1 v2) :
    pool_equ (v1.eraseIdx i) (v2.eraseIdx i) :=
  vector_remove_pointwise (fun a b : Thread E B => a = b) v1 v2 i (fun j _ => hv j)

theorem cons_pool_equ {n} (t1 t2 : Thread E B) (v1 v2 : Pool E B n) (ht : t1 = t2)
    (hv : pool_equ v1 v2) : pool_equ (Vector.cons t1 v1) (Vector.cons t2 v2) :=
  vector_cons_pointwise (fun a b : Thread E B => a = b) t1 t2 v1 v2 ht hv

/-- No hidden branch in any thread: the scheduler is a `~`-congruence only on such pools. -/
def pool_branchfree {n : Nat} (v : Pool E B n) : Prop := ∀ i : Fin n, BranchFree v[i]

theorem pool_branchfree_replace {n} (v : Pool E B n) (i : Fin n) (t : Thread E B)
    (hv : pool_branchfree v) (ht : BranchFree t) : pool_branchfree (v.set i t) :=
  vector_replace_pointwise (fun a _ : Thread E B => BranchFree a) v v i t t (fun j _ => hv j) ht

theorem pool_branchfree_step {n : Nat} (v : Pool E B n) (i : Fin n)
    (l : Label (yieldE ⊕ₑ forkE ⊕ₑ E)) (u : Thread E B)
    (hv : pool_branchfree v) (ht : CTree.trans l v[i] u) : pool_branchfree (v.set i u) :=
  pool_branchfree_replace v i u hv (branchfree_trans _ _ _ (hv i) ht)

theorem pool_branchfree_remove {n} (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (hv : pool_branchfree v) : pool_branchfree (v.eraseIdx i) :=
  vector_remove_pointwise (fun a _ : Thread E B => BranchFree a) v v i (fun j _ => hv j)

theorem pool_branchfree_cons {n} (t : Thread E B) (v : Pool E B n) (ht : BranchFree t)
    (hv : pool_branchfree v) : pool_branchfree (Vector.cons t v) :=
  vector_cons_pointwise (fun a _ : Thread E B => BranchFree a) t t v v ht hv

end PoolSBisim

section SchedulerTransitions
variable {E B : Effect.{0}} [Bn -< B] (sch : Scheduler)

theorem schedule_policy_empty_equ (v : Pool E B 0) (st : sch.sched_state) :
    schedule_policy sch 0 v none st = .ret ⟨⟩ :=
  unfold_inj (by simp)

theorem schedule_policy_focused_ret_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (st : sch.sched_state) (h : v[i].unfold = .ret ⟨⟩) :
    schedule_policy sch (n + 1) v (some i) st =
      .guard (schedule_policy sch n (v.eraseIdx i) none st) :=
  unfold_inj (by rw [schedule_policy_focused_ret sch n v i st h, unfold_guard])

theorem schedule_policy_focused_stuck_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (st : sch.sched_state) (h : v[i].unfold = .stuck) :
    schedule_policy sch (n + 1) v (some i) st = .stuck :=
  unfold_inj (by rw [schedule_policy_focused_stuck sch n v i st h, unfold_stuck])

theorem schedule_policy_focused_guard_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (st : sch.sched_state) (h : v[i].unfold = .guard t) :
    schedule_policy sch (n + 1) v (some i) st =
      .guard (schedule_policy sch (n + 1) (v.set i t) (some i) st) :=
  unfold_inj (by rw [schedule_policy_focused_guard sch n v i t st h, unfold_guard])

theorem schedule_policy_focused_step_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (st : sch.sched_state) (h : v[i].unfold = .step t) :
    schedule_policy sch (n + 1) v (some i) st =
      .step (schedule_policy sch (n + 1) (v.set i t) (some i) st) :=
  unfold_inj (by rw [schedule_policy_focused_step sch n v i t st h, unfold_step])

theorem schedule_policy_focused_br_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    {c : B.I} (k : B.O c → Thread E B) (st : sch.sched_state) (h : v[i].unfold = .br c k) :
    schedule_policy sch (n + 1) v (some i) st =
      .br c fun j => schedule_policy sch (n + 1) (v.set i (k j)) (some i) st :=
  unfold_inj (by rw [schedule_policy_focused_br sch n v i k st h, unfold_br])

theorem schedule_policy_focused_yield_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E B) (st : sch.sched_state) (h : v[i].unfold = .vis (.inl ⟨⟩) k) :
    schedule_policy sch (n + 1) v (some i) st =
      .guard (schedule_policy sch (n + 1) (v.set i (k ⟨⟩)) none st) :=
  unfold_inj (by rw [schedule_policy_focused_yield sch n v i k st h, unfold_guard])

theorem schedule_policy_focused_fork_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E B) (st : sch.sched_state) (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    schedule_policy sch (n + 1) v (some i) st =
      .guard (schedule_policy sch (n + 2) (Vector.cons (k true) (v.set i (k false)))
        (some i.succ) st) :=
  unfold_inj (by rw [schedule_policy_focused_fork sch n v i k st h, unfold_guard])

theorem schedule_policy_focused_user_event_equ (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E B) (st : sch.sched_state)
    (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    schedule_policy sch (n + 1) v (some i) st =
      .vis (.inl e) fun x => schedule_policy sch (n + 1) (v.set i (k x)) (some i) st :=
  unfold_inj (by rw [schedule_policy_focused_user_event sch n v i e k st h, unfold_vis])

/-- Unfocused selection (Rocq's dependent `match` on the arity is `br_alts`). -/
theorem schedule_policy_no_focus_equ (n : Nat) (v : Pool E B (n + 1)) (st : sch.sched_state) :
    schedule_policy sch (n + 1) v none st =
      br_alts (E := E ⊕ₑ schedE) (sch.sched_arity n st) fun a =>
        .vis (.inr (slot_index (sch.sched_pick n st a).1))
          fun _ => schedule_policy sch (n + 1) v (some (sch.sched_pick n st a).1)
            (sch.sched_pick n st a).2 :=
  schedule_policy_no_focus_nonempty sch n v st

/-- `m+1` alternatives are bisimilar to an `(m+1)`-ary hidden branch. -/
theorem br_alts_brn [LawfulSubeffect Bn B] {F : Effect.{0}} {X : Type} (m : Nat)
    (k : Fin (m + 1) → CTree F B X) : br_alts m k ~ CTree.brn (m + 1) k := by
  cases m with
  | succ m => exact sbisim_refl _
  | zero =>
    obtain ⟨y, -⟩ := LawfulSubeffect.map_surj (E₁ := Bn) (E₂ := B) (⟨1⟩ : ULift Nat)
      (⟨0⟩ : ULift (Fin 1))
    refine sbisim_symm (sb_br_l _ y _ _ fun x => ?_)
    show k (ULift.down _) ~ k 0
    rw [fin1_eq (ULift.down _)]
    exact sbisim_refl _

theorem schedule_policy_select_bisim [LawfulSubeffect Bn B] (n : Nat) (v : Pool E B (n + 1))
    (st : sch.sched_state) :
    schedule_policy sch (n + 1) v none st ~
      CTree.brn (sch.sched_arity n st + 1) fun a =>
        .vis (.inr (slot_index (sch.sched_pick n st a).1))
          fun _ => schedule_policy sch (n + 1) v (some (sch.sched_pick n st a).1)
            (sch.sched_pick n st a).2 := by
  rw [schedule_policy_no_focus_equ]
  exact br_alts_brn _ _

theorem schedule_policy_pool_proper (n : Nat) (v w : Pool E B n) (focus : Option (Fin n))
    (st : sch.sched_state) (hvw : pool_equ v w) :
    schedule_policy sch n v focus st = schedule_policy sch n w focus st := by
  rw [Vector.ext fun i h => hvw ⟨i, h⟩]

end SchedulerTransitions

section Guards
variable {E B : Effect.{u}} {X : Type u}

theorem guards_equ (n : Nat) (t u : CTree E B X) (h : t = u) : guards n t = guards n u := h ▸ rfl

theorem guards_add (n m : Nat) (t : CTree E B X) : guards (n + m) t = guards n (guards m t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_right_comm]; simp [ih]

theorem guards_guard (n : Nat) (t : CTree E B X) : guards n (.guard t) = guards (n + 1) t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [guards_succ] at ih ⊢; rw [ih]

theorem guards_trans (n : Nat) {l : Label E} {t u : CTree E B X} (h : trans l t u) :
    trans l (guards n t) u := by
  induction n with
  | zero => exact h
  | succ n ih => exact trans_guard ih

/-- Guard prefixes are cancellative. -/
theorem guards_cancel : ∀ (b c : Nat) (x y : CTree E B X), guards b x = guards c y →
    (∃ d, x = guards d y ∧ c = b + d) ∨ (∃ d, y = guards d x ∧ b = c + d) := by
  intro b
  induction b with
  | zero => intro c x y h; exact .inl ⟨c, h, by simp⟩
  | succ b ih =>
    intro c x y h
    cases c with
    | zero => exact .inr ⟨b + 1, h.symm, by omega⟩
    | succ c =>
      simp only [guards_succ, guard_eq_guard_iff] at h
      rcases ih c x y h with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
      · exact .inl ⟨d, hd, by omega⟩
      · exact .inr ⟨d, hd, by omega⟩

/-- `guard_equ` is exactly "the same tree after finitely many guards". -/
theorem guard_equ_guards (t u : CTree E B X) (h : guard_equ t u) :
    ∃ a b x, t = guards a x ∧ u = guards b x := by
  induction h with
  | rel h => rcases h with rfl | rfl
             · exact ⟨0, 0, _, rfl, rfl⟩
             · exact ⟨1, 0, _, rfl, rfl⟩
  | refl t => exact ⟨0, 0, t, rfl, rfl⟩
  | symm _ ih => obtain ⟨a, b, x, h₁, h₂⟩ := ih; exact ⟨b, a, x, h₂, h₁⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨a, b, x, rfl, hu⟩ := ih₁
    obtain ⟨c, d, y, hu', rfl⟩ := ih₂
    rcases guards_cancel b c x y (hu.symm.trans hu') with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
    · exact ⟨a + e, d, y, (guards_add a e y).symm, rfl⟩
    · exact ⟨a, d + e, x, rfl, (guards_add d e x).symm⟩

end Guards

section GuardAlignment
variable {E B : Effect.{u}} {X : Type u}

/-- One round of guard alignment: every node agrees after finitely many guards on each side; a
pure guard round consumes at least one guard on both sides (Rocq `galignF`). -/
inductive GalignF (R : Rel (CTree E B X) (CTree E B X)) : Rel (CTree E B X) (CTree E B X)
  | guard {t u} (n m : Nat) (t' u' : CTree E B X) :
      t = guards (n + 1) t' → u = guards (m + 1) u' → R t' u' → GalignF R t u
  | ret {t u} (n m : Nat) (r : X) :
      t = guards n (.ret r) → u = guards m (.ret r) → GalignF R t u
  | br {t u} (n m : Nat) (c : B.I) (k k' : B.O c → CTree E B X) :
      t = guards n (.br c k) → u = guards m (.br c k') → (∀ i, R (k i) (k' i)) → GalignF R t u
  | vis {t u} (n m : Nat) (e : E.I) (k k' : E.O e → CTree E B X) :
      t = guards n (.vis e k) → u = guards m (.vis e k') → (∀ x, R (k x) (k' x)) →
      GalignF R t u
  | stuck {t u} (n m : Nat) : t = guards n .stuck → u = guards m .stuck → GalignF R t u
  | step {t u} (n m : Nat) (t' u' : CTree E B X) :
      t = guards n (.step t') → u = guards m (.step u') → R t' u' → GalignF R t u

/-- The functor of `galigned`. -/
def galignF : Mon (Rel (CTree E B X) (CTree E B X)) where
  body := GalignF
  mono h _ _
    | .guard n m t' u' ht hu hR => .guard n m t' u' ht hu (h _ _ hR)
    | .ret n m r ht hu => .ret n m r ht hu
    | .br n m c k k' ht hu hR => .br n m c k k' ht hu fun i => h _ _ (hR i)
    | .vis n m e k k' ht hu hR => .vis n m e k k' ht hu fun x => h _ _ (hR x)
    | .stuck n m ht hu => .stuck n m ht hu
    | .step n m t' u' ht hu hR => .step n m t' u' ht hu (h _ _ hR)

/-- Alignment up to finitely many leading guards (Rocq coinductive `galigned`). It implies `~`. -/
def galigned : Rel (CTree E B X) (CTree E B X) := gfp (galignF (E := E) (B := B) (X := X))

theorem galigned_unfold {t u : CTree E B X} : galigned t u ↔ GalignF galigned t u :=
  ⟨fun h => gfp_pfp (b := galignF) t u h, fun h => b_chain (gfp_chain galignF) t u h⟩

/-- Coinduction principle for guard alignment. -/
theorem galigned_coind (R : Rel (CTree E B X) (CTree E B X)) (h : ∀ t u, R t u → GalignF R t u)
    (t u : CTree E B X) (hR : R t u) : galigned t u :=
  le_gfp (b := galignF) (x := R) h t u hR

theorem galign_guard {t u : CTree E B X} (n m : Nat) (t' u' : CTree E B X)
    (ht : t = guards (n + 1) t') (hu : u = guards (m + 1) u') (h : galigned t' u') :
    galigned t u := galigned_unfold.2 (.guard n m t' u' ht hu h)

theorem galign_ret {t u : CTree E B X} (n m : Nat) (r : X) (ht : t = guards n (.ret r))
    (hu : u = guards m (.ret r)) : galigned t u := galigned_unfold.2 (.ret n m r ht hu)

theorem galign_br {t u : CTree E B X} (n m : Nat) (c : B.I) (k k' : B.O c → CTree E B X)
    (ht : t = guards n (.br c k)) (hu : u = guards m (.br c k')) (h : ∀ i, galigned (k i) (k' i)) :
    galigned t u := galigned_unfold.2 (.br n m c k k' ht hu h)

theorem galign_vis {t u : CTree E B X} (n m : Nat) (e : E.I) (k k' : E.O e → CTree E B X)
    (ht : t = guards n (.vis e k)) (hu : u = guards m (.vis e k'))
    (h : ∀ x, galigned (k x) (k' x)) : galigned t u := galigned_unfold.2 (.vis n m e k k' ht hu h)

theorem galign_stuck {t u : CTree E B X} (n m : Nat) (ht : t = guards n .stuck)
    (hu : u = guards m .stuck) : galigned t u := galigned_unfold.2 (.stuck n m ht hu)

theorem galign_step {t u : CTree E B X} (n m : Nat) (t' u' : CTree E B X)
    (ht : t = guards n (.step t')) (hu : u = guards m (.step u')) (h : galigned t' u') :
    galigned t u := galigned_unfold.2 (.step n m t' u' ht hu h)

theorem galigned_equ (t u a b : CTree E B X) (ht : t = a) (hu : u = b) (h : galigned t u) :
    galigned a b := ht ▸ hu ▸ h

theorem galigned_sym (t u : CTree E B X) (h : galigned t u) : galigned u t := by
  refine galigned_coind (fun u t => galigned t u) ?_ u t h
  intro u t h
  match galigned_unfold.1 h with
  | .guard n m t' u' ht hu h => exact .guard m n u' t' hu ht h
  | .ret n m r ht hu => exact .ret m n r hu ht
  | .br n m c k k' ht hu h => exact .br m n c k' k hu ht h
  | .vis n m e k k' ht hu h => exact .vis m n e k' k hu ht h
  | .stuck n m ht hu => exact .stuck m n hu ht
  | .step n m t' u' ht hu h => exact .step m n u' t' hu ht h

theorem galigned_stuck : galigned (.stuck : CTree E B X) .stuck := galign_stuck 0 0 rfl rfl

theorem galigned_refl (t : CTree E B X) : galigned t t := by
  refine galigned_coind (fun a b => a = b) ?_ t t rfl
  rintro t _ rfl
  have e := observe_equ_go t _ rfl
  generalize t.unfold = ot at e
  subst e
  cases ot with
  | ret r => exact .ret 0 0 r rfl rfl
  | stuck => exact .stuck 0 0 rfl rfl
  | step s => exact .step 0 0 s s rfl rfl rfl
  | guard g => exact .guard 0 0 g g rfl rfl rfl
  | vis e k => exact .vis 0 0 e k k rfl rfl fun _ => rfl
  | br c k => exact .br 0 0 c k k rfl rfl fun _ => rfl

/-- Replay a transition of the left tree on an aligned right tree. Rocq's `go T` is a tree `t`
with `t.unfold = T`. -/
theorem galigned_match {l : Label E} {T : CTreeF E B X (CTree E B X)} {next : CTree E B X}
    (tr : Trans_ l T next) :
    ∀ t u, t.unfold = T → galigned t u → ∃ u', trans l u u' ∧ galigned next u' := by
  induction tr with
  | br x _ ih =>
    intro t u ht h
    rcases galigned_unfold.1 h with ⟨n, m, t', u', rfl, rfl, ha⟩ | ⟨n, m, r, rfl, rfl⟩ |
      ⟨n, m, c, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, e, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, rfl, rfl⟩ |
      ⟨n, m, t', u', rfl, rfl, ha⟩
    · simp at ht
    · cases n <;> simp at ht
    · cases n with
      | succ n => simp at ht
      | zero =>
        simp only [guards_zero, unfold_br] at ht
        cases ht
        obtain ⟨v, hv, hn⟩ := ih _ _ rfl (ha x)
        exact ⟨v, guards_trans m (trans_br x hv), hn⟩
    · cases n <;> simp at ht
    · cases n <;> simp at ht
    · cases n <;> simp at ht
  | guard _ ih =>
    intro t u ht h
    rcases galigned_unfold.1 h with ⟨n, m, t', u', rfl, rfl, ha⟩ | ⟨n, m, r, rfl, rfl⟩ |
      ⟨n, m, c, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, e, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, rfl, rfl⟩ |
      ⟨n, m, t', u', rfl, rfl, ha⟩
    · simp only [guards_succ, unfold_guard, CTreeF.guard.injEq] at ht
      subst ht
      cases n with
      | zero =>
        obtain ⟨v, hv, hn⟩ := ih t' u' rfl ha
        exact ⟨v, guards_trans (m + 1) hv, hn⟩
      | succ n => exact ih _ _ rfl (galign_guard n m t' u' rfl rfl ha)
    all_goals
      cases n with
      | zero => simp at ht
      | succ n =>
        simp only [guards_succ, unfold_guard, CTreeF.guard.injEq] at ht
        subst ht
        refine ih _ _ rfl ?_
        first
          | exact galign_ret n m _ rfl rfl
          | exact galign_br n m _ _ _ rfl rfl ha
          | exact galign_vis n m _ _ _ rfl rfl ha
          | exact galign_stuck n m rfl rfl
          | exact galign_step n m _ _ rfl rfl ha
  | step =>
    intro t u ht h
    rcases galigned_unfold.1 h with ⟨n, m, t', u', rfl, rfl, ha⟩ | ⟨n, m, r, rfl, rfl⟩ |
      ⟨n, m, c, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, e, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, rfl, rfl⟩ |
      ⟨n, m, t', u', rfl, rfl, ha⟩
    · simp at ht
    · cases n <;> simp at ht
    · cases n <;> simp at ht
    · cases n <;> simp at ht
    · cases n <;> simp at ht
    · cases n with
      | succ n => simp at ht
      | zero =>
        simp only [guards_zero, unfold_step, CTreeF.step.injEq] at ht
        subst ht
        exact ⟨u', guards_trans m (trans_step u'), ha⟩
  | obs x =>
    intro t u ht h
    rcases galigned_unfold.1 h with ⟨n, m, t', u', rfl, rfl, ha⟩ | ⟨n, m, r, rfl, rfl⟩ |
      ⟨n, m, c, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, e, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, rfl, rfl⟩ |
      ⟨n, m, t', u', rfl, rfl, ha⟩
    · simp at ht
    · cases n <;> simp at ht
    · cases n <;> simp at ht
    · cases n with
      | succ n => simp at ht
      | zero =>
        simp only [guards_zero, unfold_vis] at ht
        cases ht
        exact ⟨k1' x, guards_trans m (trans_vis x k1'), ha x⟩
    · cases n <;> simp at ht
    · cases n <;> simp at ht
  | val =>
    intro t u ht h
    rcases galigned_unfold.1 h with ⟨n, m, t', u', rfl, rfl, ha⟩ | ⟨n, m, r, rfl, rfl⟩ |
      ⟨n, m, c, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, e, k1, k1', rfl, rfl, ha⟩ | ⟨n, m, rfl, rfl⟩ |
      ⟨n, m, t', u', rfl, rfl, ha⟩
    · simp at ht
    · cases n with
      | succ n => simp at ht
      | zero =>
        simp only [guards_zero, unfold_ret, CTreeF.ret.injEq] at ht
        subst ht
        exact ⟨.stuck, guards_trans m (trans_ret r), galigned_stuck⟩
    · cases n <;> simp at ht
    · cases n <;> simp at ht
    · cases n <;> simp at ht
    · cases n <;> simp at ht

theorem galigned_trans (t u next : CTree E B X) (l : Label E) (h : galigned t u)
    (tr : trans l t next) : ∃ other, trans l u other ∧ galigned next other :=
  galigned_match tr t u rfl h

theorem galigned_sbisim (t u : CTree E B X) (h : galigned t u) : t ~ u := by
  refine le_gfp (b := sb Eq) (x := galigned) (fun t u h => ⟨?_, ?_⟩) t u h
  · intro l next tr
    obtain ⟨other, tr', ha⟩ := galigned_trans t u next l h tr
    exact ⟨l, other, tr', ha, rfl⟩
  · intro l next tr
    obtain ⟨other, tr', ha⟩ := galigned_trans u t next l (galigned_sym t u h) tr
    exact ⟨l, other, tr', galigned_sym _ _ ha, rfl⟩

end GuardAlignment

theorem guards_shift {E B : Effect.{u}} {X : Type u} (n a : Nat) (t : CTree E B X) :
    guards n (guards (a + 1) t) = guards (n + a + 1) t :=
  (guards_add n (a + 1) t).symm

end Yield
end Tisl

-- Not ported: `guard_equ_proper`, `guards_proper` (`Proper` over `equ`, i.e. equality);
-- Rocq's separate coinductive `galigned` and its `galign_*` constructors are the theorems
-- `galign_*` over `galigned := gfp galignF`, so `galigned_coind` is `le_gfp`.
-- `schedule_policy_no_focus_observe` (same statement as `schedule_policy_no_focus_equ` once `≅` is
-- `=`).
