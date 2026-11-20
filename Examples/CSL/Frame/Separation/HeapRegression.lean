/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Asep
public import Logic.Sep.Asep

/-!
# Heap regressions for the CoCSL owned machine

Concrete forked programs over `init_owned`/`project`: nested-fork lineage under insertion,
removal and both schedules; CAS and free success; faults after free; and a foreign read that is
not confined although the joined runner reads it (← `examples/CSL/Frame/Separation.v`, module
`HeapRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation.HeapRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm CoCSL

/-! ## One-step constructors of the owned machine and reachability -/

def reach : OwnedCfg → OwnedCfg → Prop := Star owned_next

theorem ostep_select (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) :
    c.pool = mk_pool (n + 1) v g none →
    owned_step c (act g[j] .select) (set_pool c (mk_pool (n + 1) v g (some j))) :=
  fun H => (owned_step_sel _ _ _ _ _ _ H).2 ⟨j, rfl, rfl⟩

theorem ostep_yield (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (k : PUnit → Thread sE Bn) (v' : Pool sE Bn (n + 1)) :
    c.pool = mk_pool (n + 1) v g (some j) →
    v[j] = .vis (E := CEff) (.inl ⟨⟩) k → v.set j (k ⟨⟩) = v' →
    owned_step c (act g[j] .yield) (set_pool c (mk_pool (n + 1) v' g none)) := by
  rintro H Hh rfl
  exact (owned_step_focus _ _ _ _ _ _ _ H).2 (.inr (.inl ⟨k, ⟨0, Hh⟩, rfl, rfl⟩))

theorem ostep_fork (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (k : Bool → Thread sE Bn) (v' : Pool sE Bn (n + 1)) :
    c.pool = mk_pool (n + 1) v g (some j) →
    v[j] = .vis (E := CEff) (.inr (.inl ⟨⟩)) k → v.set j (k false) = v' →
    owned_step c (act g[j] .fork)
      (set_pool c (mk_pool (n + 2) (Vector.cons (k true) v') (Vector.cons g[j] g)
        (some j.succ))) := by
  rintro H Hh rfl
  exact (owned_step_focus _ _ _ _ _ _ _ H).2 (.inr (.inr (.inl ⟨k, ⟨0, Hh⟩, rfl, rfl⟩)))

theorem ostep_ret (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (v' : Pool sE Bn n) (g' : Vector Side n) :
    c.pool = mk_pool (n + 1) v g (some j) →
    v[j] = pure ⟨⟩ → vector_remove v j = v' → vector_remove g j = g' →
    owned_step c (act g[j] .ret) (set_pool c (mk_pool n v' g' none)) := by
  rintro H Hh rfl rfl
  exact (owned_step_focus _ _ _ _ _ _ _ H).2 (.inr (.inr (.inr (.inl ⟨⟨0, Hh⟩, rfl, rfl⟩))))

theorem ostep_prim (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (e : sE.I) (k : sE.O e → Thread sE Bn) (kind : OwnedKind) (y : sE.O e)
    (c1 : OwnedCfg) (v' : Pool sE Bn (n + 1)) :
    c.pool = mk_pool (n + 1) v g (some j) →
    v[j] = .vis (E := CEff) (.inr (.inr e)) k →
    prim_step g[j] c e = some (kind, y, c1) → v.set j (k y) = v' →
    owned_step c (act g[j] kind) (set_pool c1 (mk_pool (n + 1) v' g (some j))) := by
  rintro H Hh Hp rfl
  exact (owned_step_focus _ _ _ _ _ _ _ H).2
    (.inr (.inr (.inr (.inr ⟨e, k, kind, y, c1, ⟨0, Hh⟩, Hp, rfl, rfl⟩))))

theorem reach_step (c : OwnedCfg) (a : OwnedAction) (c' d : OwnedCfg) :
    owned_step c a c' → reach c' d → reach c d :=
  fun H R => Star.trans (Star.single ⟨a, H⟩) R

theorem reach_wf (c d : OwnedCfg) : owned_wf c → reach c d → owned_wf d :=
  fun Hc R => clos_refl_trans_preserves _ _ (fun x y Hx ⟨a, Hs⟩ => owned_step_wf x a y Hx Hs)
    c d Hc R

/-! ## Source heads -/

theorem denote_write_head (a v : Nat) :
    denote (.write a v) = .vis (E := CEff) (.inr (.inr (.inl (.write a v)))) fun _ => pure ⟨⟩ :=
  source_raw_write_head a v _

theorem denote_free_head (b : Nat) :
    denote (.free b) = .vis (E := CEff) (.inr (.inr (.inl (.free b)))) fun _ => pure ⟨⟩ :=
  source_raw_free_head b _

theorem denote_cas_bind_head (a old desired : Nat) (next : Bool → CProg Unit) :
    denote (.bind (.cas (.lit a) (.lit old) (.lit desired)) next) =
      .vis (E := CEff) (.inr (.inr (.inl (.cas a old desired)))) fun b => denote (next b) := by
  rw [denote, source_raw_bind]; exact source_raw_cas_head a old desired _

theorem denote_yield_head : denote .yield = .vis (E := CEff) (.inl ⟨⟩) fun _ => pure ⟨⟩ :=
  source_raw_yield_head _

theorem denote_yield_bind_head (next : Unit → CProg Unit) :
    denote (.bind .yield next) = .vis (E := CEff) (.inl ⟨⟩) fun _ => denote (next ()) := by
  rw [denote, source_raw_bind]; exact source_raw_yield_head _

theorem denote_free_bind_head (b : Nat) (next : Unit → CProg Unit) :
    denote (.bind (.free b) next) =
      .vis (E := CEff) (.inr (.inr (.inl (.free b)))) fun _ => denote (next ()) := by
  rw [denote, source_raw_bind]; exact source_raw_free_head b _

/-! Rocq's `head`, `ostep`, `oselect` and `owned_equ_proj` tactics, as local macros. -/

/-- Close `v[j] = <head>` for a concrete source slot. -/
local macro "head" : tactic => `(tactic| first
  | exact denote_write_head _ _ | exact denote_read_bind _ _ | exact denote_free_head _
  | exact denote_cas_bind_head _ _ _ _ | exact denote_yield_bind_head _
  | exact denote_yield_head | exact denote_free_bind_head _ _ | exact denote_fork_bind _ _
  | exact rfl)

/-- Close `vector_remove v j = ?w` with `?w` a literal vector. -/
local macro "vremove" : tactic => `(tactic| ((simp only [vector_remove, Vector.set_mk,
  List.set_toArray, List.set_cons_succ, List.set_cons_zero, Vector.eraseIdx_mk,
  List.eraseIdx_toArray, List.eraseIdx_cons_succ, List.eraseIdx_zero, List.tail_cons,
  Nat.add_one_sub_one]) <;> try exact rfl))

/-- One concrete action of the focused slot. -/
local macro "ostep" : tactic => `(tactic| (apply reach_step; focus first
  | (apply ostep_prim; exact rfl; head; exact rfl; exact rfl)
  | (apply ostep_ret; exact rfl; exact rfl; vremove; vremove)
  | (apply ostep_yield; exact rfl; head; exact rfl)
  | (apply ostep_fork; exact rfl; head; exact rfl)))

/-- Select slot `j` of an unfocused pool. -/
local macro "oselect " j:term : tactic =>
  `(tactic| (apply reach_step; focus (apply ostep_select; exact $j; exact rfl)))

/-- Compute the slot list of a projection of a literal pool. -/
local macro "slots_simp" : tactic => `(tactic|
  ((simp [tp_slots, project, project_pool, proj_slots, proj_indices, fin_all, List.finRange,
    List.ofFn_succ, set_pool, mk_pool, Vector.cons, side_eqb]) <;> decide))

/-- `(project i c).pool = mk_pool …` for a literal pool. -/
local macro "proj_pool" : tactic => `(tactic|
  exact tp_equ_eq ⟨Forall2_slot_iff.2 (by slots_simp), rfl⟩)

/-- `owned_equ` of two projections with computable pools (unfold the named configurations
first). -/
local macro "owned_equ_proj" : tactic => `(tactic|
  (refine ⟨⟨Forall2_slot_iff.2 ?_, rfl⟩, ?_, ?_, rfl, rfl, ?_, ?_⟩
   · slots_simp
   all_goals intro i; cases i <;> first | exact peq_refl _ | rfl))

/-! ## Nested fork: lineage under insertion, removal and both schedules -/

/-- The child forks a writer of cell `1`, yields, and writes cell `1` again; the parent writes
its own cell `2`. -/
def nchild : CProg Unit := .bind (.fork (.write 1 1)) fun _ => .bind .yield fun _ => .write 1 2
def nparent : CProg Unit := .write 2 8
def nh : ManagedHeap := (hsingle 1 0, hemp)
def nh' : ManagedHeap := (hsingle 2 7, hemp)
def n0 : OwnedCfg := init_owned nchild nparent nh nh' [] 0

theorem nested_admissible : admissible nchild nparent nh nh' [] 0 := by
  apply admissible_intro
  · exact managed_wf_preallocated _
  · exact managed_wf_preallocated _
  · exact ⟨hsingle_disj _ _ _ _ (by decide), hdisj_hemp _⟩
  · exact ⟨⟨trivial, trivial⟩, fun _ => ⟨trivial, fun _ => trivial⟩⟩
  · exact trivial
  · simp [nchild, addr_ok, nh, hsingle]
  · simp [nparent, addr_ok, nh', hsingle]

theorem n0_wf : owned_wf n0 :=
  init_owned_wf _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _)
    ⟨hsingle_disj _ _ _ _ (by decide), hdisj_hemp _⟩

/-- The parent wrote and returned; the child is selected before its fork. -/
def n_fork : OwnedCfg :=
  set_pool (set_heap n0 .parent (upd (hsingle 2 7) 2 8, hemp))
    (mk_pool 1 #v[denote nchild] #v[.child] (some 0))

theorem n_fork_reach : reach n0 n_fork := by
  ostep; ostep; oselect 0; exact Star.refl

/-- The nested fork inserts the spawned writer in front, tags both descendants `child`, keeps
the forker focused, and leaves the parent projection unchanged. -/
theorem nested_fork_insert (a : OwnedAction) (c' : OwnedCfg) :
    owned_step n_fork a c' →
    a = act .child .fork ∧
    (∃ k : Bool → Thread sE Bn,
      (∀ b, k b = if b then denote (.write 1 1) else denote (.bind .yield fun _ => .write 1 2)) ∧
      c' = set_pool n_fork (mk_pool 2 #v[k true, k false] #v[.child, .child] (some 1))) ∧
    (project .child c').pool.size = 2 ∧
    owned_equ (project .parent c') (project .parent n_fork) := by
  intro H
  rw [owned_step_focus _ 0 #v[denote nchild] #v[.child] 0 _ _ rfl,
    focus_step_head_fork n_fork 0 #v[denote nchild] #v[.child] 0 _ 0 _ _
      (denote_fork_bind _ _)] at H
  obtain ⟨k, Hk, rfl, rfl⟩ := H
  refine ⟨rfl, ⟨k, Hk, rfl⟩, rfl, ?_⟩
  unfold n_fork; owned_equ_proj

/-- After the fork and the forker's yield: two `child` writers, unfocused. -/
def n_sched : OwnedCfg :=
  set_pool n_fork (mk_pool 2 #v[denote (.write 1 1), denote (.write 1 2)] #v[.child, .child] none)

theorem n_sched_reach : reach n0 n_sched :=
  Star.trans n_fork_reach (by ostep; ostep; exact Star.refl)

/-- The two legal schedules after the inserted yield: select either `child` writer. -/
theorem nested_schedules (a : OwnedAction) (c' : OwnedCfg) :
    owned_step n_sched a c' →
    a = act .child .select ∧
    (c' = set_pool n_sched (mk_pool 2 #v[denote (.write 1 1), denote (.write 1 2)]
        #v[.child, .child] (some 0)) ∨
     c' = set_pool n_sched (mk_pool 2 #v[denote (.write 1 1), denote (.write 1 2)]
        #v[.child, .child] (some 1))) := by
  intro H
  rw [owned_step_sel _ 1 #v[denote (.write 1 1), denote (.write 1 2)] #v[.child, .child] _ _
    rfl] at H
  obtain ⟨⟨_ | _ | j, hj⟩, rfl, rfl⟩ := H
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inr rfl⟩
  · omega

/-- The spawned writer finished: its removal keeps the survivor `child`. -/
def n_remove : OwnedCfg :=
  set_pool (set_heap n_sched .child (upd (hsingle 1 0) 1 1, hemp))
    (mk_pool 2 #v[pure ⟨⟩, denote (.write 1 2)] #v[.child, .child] (some 0))

theorem n_remove_reach : reach n0 n_remove :=
  Star.trans n_sched_reach (by oselect 0; ostep; exact Star.refl)

theorem nested_remove (a : OwnedAction) (c' : OwnedCfg) :
    owned_step n_remove a c' →
    a = act .child .ret ∧
    c' = set_pool n_remove (mk_pool 1 #v[denote (.write 1 2)] #v[.child] none) ∧
    owned_equ (project .parent c') (project .parent n_fork) := by
  intro H
  rw [owned_step_focus _ 1 #v[pure ⟨⟩, denote (.write 1 2)] #v[.child, .child] 0 _ _ rfl,
    focus_step_head_ret n_remove 1 #v[pure ⟨⟩, denote (.write 1 2)] #v[.child, .child] 0 0 _ _
      rfl] at H
  obtain ⟨rfl, rfl⟩ := H
  refine ⟨rfl, by vremove, ?_⟩
  unfold n_remove n_sched n_fork; vremove; owned_equ_proj

/-- Both schedules terminate, keep ownership and the parent projection, and race within the
child lineage: cell `1` ends at `2` or at `1`. -/
theorem nested_schedule_spawned_first :
    ∃ d, reach n_sched d ∧ d.pool.size = 0 ∧ owned_wf d ∧
      (d.heap .child).1 1 = some 2 ∧ (d.heap .parent).1 2 = some 8 ∧
      owned_equ (project .parent d) (project .parent n_fork) := by
  apply Exists.intro
  refine ⟨?r, ?_, ?wf, ?_, ?_, ?e⟩
  case r => oselect 0; ostep; ostep; oselect 0; ostep; ostep; exact Star.refl
  any_goals rfl
  case wf =>
    refine reach_wf _ _ n0_wf (Star.trans n_sched_reach ?_)
    oselect 0; ostep; ostep; oselect 0; ostep; ostep; exact Star.refl
  case e => unfold n_sched n_fork; owned_equ_proj

theorem nested_schedule_forker_first :
    ∃ d, reach n_sched d ∧ d.pool.size = 0 ∧ owned_wf d ∧
      (d.heap .child).1 1 = some 1 ∧ (d.heap .parent).1 2 = some 8 ∧
      owned_equ (project .parent d) (project .parent n_fork) := by
  apply Exists.intro
  refine ⟨?r, ?_, ?wf, ?_, ?_, ?e⟩
  case r => oselect 1; ostep; ostep; oselect 0; ostep; ostep; exact Star.refl
  any_goals rfl
  case wf =>
    refine reach_wf _ _ n0_wf (Star.trans n_sched_reach ?_)
    oselect 1; ostep; ostep; oselect 0; ostep; ostep; exact Star.refl
  case e => unfold n_sched n_fork; owned_equ_proj

/-! ## Free, CAS and faults on allocated blocks -/

def bC : ManagedHeap := (hsingle 1 0, hsingle 1 1)
def bP : ManagedHeap := (hsingle 2 7, hsingle 2 1)

theorem managed_wf_block (a v : Nat) : 0 < a → managed_wf (hsingle a v, hsingle a 1) := by
  intro Ha
  refine ⟨fun b n Hb => ?_, fun b1 n1 b2 n2 H1 H2 Hne => ?_⟩
  · simp only [hsingle] at Hb ⊢
    by_cases h : a = b
    · subst h; simp at Hb; subst Hb
      refine ⟨Ha, by omega, fun x Hx => ?_⟩
      have : x = a := by omega
      simp [this]
    · simp [h] at Hb
  · simp only [hsingle] at H1 H2
    by_cases h1 : a = b1 <;> by_cases h2 : a = b2 <;> simp_all

theorem blocks_disj : bC # bP :=
  ⟨hsingle_disj _ _ _ _ (by decide), hsingle_disj _ _ _ _ (by decide)⟩

/-- The parent yields at once; the child is then selected while the parent block stays live. -/
def b0 (p : CProg Unit) : OwnedCfg := init_owned p .yield bC bP [] 0
def bfocus (p : CProg Unit) : OwnedCfg :=
  set_pool (b0 p) (mk_pool 2 #v[denote p, pure ⟨⟩] #v[.child, .parent] (some 0))

theorem bfocus_reach (p : CProg Unit) : reach (b0 p) (bfocus p) := by
  ostep; oselect 0; exact Star.refl

theorem bfocus_coupled (p : CProg Unit) : component_ok p → addr_ok bC p → coupled (bfocus p) :=
  fun Hok Haddr => ⟨p, .yield, bC, bP, [], 0, bfocus p,
    admissible_intro _ _ _ _ _ _ (managed_wf_block 1 0 (by decide))
      (managed_wf_block 2 7 (by decide)) blocks_disj Hok trivial Haddr trivial,
    bfocus_reach p, owned_equ_Equivalence.refl _⟩

theorem prim_read_none (c : OwnedCfg) (a : Nat) :
    (c.heap .child).1 a = none → prim_step .child c (.inl (.read a)) = none := by
  intro H; simp [prim_step, heap_prim, H]

theorem prim_free_none (c : OwnedCfg) (b : Nat) :
    managed_free (c.heap .child) b = none → prim_step .child c (.inl (.free b)) = none := by
  intro H; simp [prim_step, heap_prim, H]

/-! ### CAS -/

def pcas_ok : CProg Unit := .bind (.cas (.lit 1) (.lit 0) (.lit 5)) fun _ => .ret ()
def pcas_fail : CProg Unit := .bind (.cas (.lit 1) (.lit 3) (.lit 5)) fun _ => .ret ()

theorem cas_success_response :
    prim_step .child (bfocus pcas_ok) (.inl (.cas 1 0 5)) =
      some (.cas true, true,
        set_heap (bfocus pcas_ok) .child (upd (hsingle 1 0) 1 5, hsingle 1 1)) :=
  rfl

/-- A successful CAS answers `true` and changes only cell `1` of the child. -/
theorem cas_success_step (a : OwnedAction) (c' : OwnedCfg) :
    owned_step (bfocus pcas_ok) a c' →
    a = act .child (.cas true) ∧
    (∃ k : Bool → Thread sE Bn, (∀ b, k b = denote (.ret ())) ∧
      c' = set_pool (set_heap (bfocus pcas_ok) .child (upd (hsingle 1 0) 1 5, hsingle 1 1))
        (mk_pool 2 #v[k true, pure ⟨⟩] #v[.child, .parent] (some 0))) ∧
    (c'.heap .child).1 1 = some 5 ∧
    (∀ x, x ≠ 1 → (c'.heap .child).1 x = bC.1 x) ∧
    (c'.heap .child).2 = bC.2 ∧ c'.heap .parent = bP := by
  intro H
  rw [owned_step_focus _ 1 #v[denote pcas_ok, pure ⟨⟩] #v[.child, .parent] 0 _ _ rfl,
    focus_step_head_prim (bfocus pcas_ok) 1 #v[denote pcas_ok, pure ⟨⟩] #v[.child, .parent] 0
      _ _ 0 _ _ (denote_cas_bind_head 1 0 5 _)] at H
  obtain ⟨k, kind, y, c1, Hk, Hp, rfl, rfl⟩ := H
  change prim_step .child (bfocus pcas_ok) (.inl (.cas 1 0 5)) = some (kind, y, c1) at Hp
  rw [cas_success_response] at Hp
  simp only [Option.some.injEq, Prod.mk.injEq] at Hp
  obtain ⟨rfl, rfl, rfl⟩ := Hp
  exact ⟨rfl, ⟨k, Hk, rfl⟩, rfl, fun x Hx => upd_neq _ _ _ _ Hx, rfl, rfl⟩

theorem cas_failure_response :
    prim_step .child (bfocus pcas_fail) (.inl (.cas 1 3 5)) =
      some (.cas false, false, bfocus pcas_fail) :=
  rfl

/-- A failed CAS answers `false` and leaves both heaps unchanged. -/
theorem cas_failure_step (a : OwnedAction) (c' : OwnedCfg) :
    owned_step (bfocus pcas_fail) a c' →
    a = act .child (.cas false) ∧
    (∃ k : Bool → Thread sE Bn, (∀ b, k b = denote (.ret ())) ∧
      c' = set_pool (bfocus pcas_fail) (mk_pool 2 #v[k false, pure ⟨⟩] #v[.child, .parent]
        (some 0))) ∧
    c'.heap .child = bC ∧ c'.heap .parent = bP := by
  intro H
  rw [owned_step_focus _ 1 #v[denote pcas_fail, pure ⟨⟩] #v[.child, .parent] 0 _ _ rfl,
    focus_step_head_prim (bfocus pcas_fail) 1 #v[denote pcas_fail, pure ⟨⟩] #v[.child, .parent] 0
      _ _ 0 _ _ (denote_cas_bind_head 1 3 5 _)] at H
  obtain ⟨k, kind, y, c1, Hk, Hp, rfl, rfl⟩ := H
  change prim_step .child (bfocus pcas_fail) (.inl (.cas 1 3 5)) = some (kind, y, c1) at Hp
  rw [cas_failure_response] at Hp
  simp only [Option.some.injEq, Prod.mk.injEq] at Hp
  obtain ⟨rfl, rfl, rfl⟩ := Hp
  exact ⟨rfl, ⟨k, Hk, rfl⟩, rfl, rfl⟩

/-! ### Free and faults after free -/

def pfree_read : CProg Unit := .bind (.free 1) fun _ => .bind (.read 1) fun _ => .ret ()
def pfree_twice : CProg Unit := .bind (.free 1) fun _ => .free 1
def pfree0 : CProg Unit := .free 0

/-- The child's block after `free 1`. -/
def freed : ManagedHeap := (hfree_block 1 1 (hsingle 1 0), hfree 1 (hsingle 1 1))

theorem freed_empty : (∀ x, freed.1 x = none) ∧ (∀ b, freed.2 b = none) := by
  constructor <;> intro x <;> simp only [freed, hfree_block, hfree, hsingle] <;>
    by_cases h : 1 = x <;> simp [h] <;> omega

theorem free_response (p : CProg Unit) :
    prim_step .child (bfocus p) (.inl (.free 1)) =
      some (.free 1, ⟨⟩, set_heap (bfocus p) .child freed) :=
  rfl

/-- `free 1` removes the child's data and extent, keeps the parent block, and continues with the
rest of the child. -/
theorem free_step (next : Unit → CProg Unit) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step (bfocus (.bind (.free 1) next)) a c' →
    a = act .child (.free 1) ∧
    (∃ t, t = denote (next ()) ∧
      c' = set_pool (set_heap (bfocus (.bind (.free 1) next)) .child freed)
        (mk_pool 2 #v[t, pure ⟨⟩] #v[.child, .parent] (some 0))) ∧
    c'.heap .child = freed ∧ c'.heap .parent = bP := by
  intro H
  rw [owned_step_focus _ 1 #v[denote (.bind (.free 1) next), pure ⟨⟩] #v[.child, .parent] 0 _ _
      rfl,
    focus_step_head_prim _ 1 #v[denote (.bind (.free 1) next), pure ⟨⟩] #v[.child, .parent] 0
      _ _ 0 _ _ (denote_free_bind_head 1 next)] at H
  obtain ⟨k, kind, y, c1, Hk, Hp, rfl, rfl⟩ := H
  change prim_step .child (bfocus (.bind (.free 1) next)) (.inl (.free 1)) =
    some (kind, y, c1) at Hp
  rw [free_response] at Hp
  simp only [Option.some.injEq, Prod.mk.injEq] at Hp
  obtain ⟨rfl, -, rfl⟩ := Hp
  exact ⟨rfl, ⟨k y, Hk y, rfl⟩, rfl, rfl⟩

theorem bfocus_free_read_coupled : coupled (bfocus pfree_read) :=
  bfocus_coupled _ ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩
    (by simp [pfree_read, addr_ok, bC, hsingle])

theorem bfocus_free_twice_coupled : coupled (bfocus pfree_twice) :=
  bfocus_coupled _ ⟨trivial, fun _ => trivial⟩ (by simp [pfree_twice, addr_ok, bC, hsingle])

/-- After `free 1`, reading cell `1` faults: no owned action, no action of the child's
projection, and the canonical runner on the joined heap is stuck rather than reading the parent's
memory. -/
theorem free_read_faults (a : OwnedAction) (c' : OwnedCfg) :
    owned_step (bfocus pfree_read) a c' →
    (∀ a' c'', ¬ owned_step c' a' c'') ∧
    (∀ a' c'', ¬ owned_step (project .child c') a' c'') ∧
    isStuck (owned_interp c') := by
  intro H
  obtain ⟨-, ⟨t, rfl, rfl⟩, -⟩ := free_step _ _ _ H
  have Hh := denote_read_bind 1 fun _ => .ret ()
  have Hrun : isStuck (interp_schedule_nd sh 2 #v[denote (.bind (.read 1) fun _ => .ret ()),
      pure ⟨⟩] (some 0) ((hunion freed.1 bP.1, hunion freed.2 bP.2), ([], 0))) := by
    rw [show denote (.bind (.read 1) fun _ => .ret ()) = _ from
      source_raw_bind (.read 1) (fun _ => .ret ()) fun _ => pure ⟨⟩]
    exact isStuck_sbisim (interp_nd_source_read_missing 1 #v[pure ⟨⟩, pure ⟨⟩] 0 1 _ _ _ [] 0 rfl)
      stuck_isStuck
  refine ⟨fun a' c'' H' => ?_, fun a' c'' H' => ?_, Hrun⟩
  · rw [owned_step_focus _ 1 _ #v[.child, .parent] 0 _ _ rfl,
      focus_step_head_prim _ 1 _ #v[.child, .parent] 0 _ _ 0 _ _ Hh] at H'
    obtain ⟨k, kind, y, c1, -, Hp, -⟩ := H'
    cases (prim_read_none _ 1 rfl).symm.trans Hp
  · rw [owned_step_focus _ 0 #v[denote (.bind (.read 1) fun _ => .ret ())] #v[.child] 0 _ _
        (by proj_pool),
      focus_step_head_prim _ 0 _ #v[.child] 0 _ _ 0 _ _ Hh] at H'
    obtain ⟨k, kind, y, c1, -, Hp, -⟩ := H'
    cases (prim_read_none _ 1 rfl).symm.trans Hp

/-- A second `free 1` faults the same way: it does not free the parent's block. -/
theorem free_twice_faults (a : OwnedAction) (c' : OwnedCfg) :
    owned_step (bfocus pfree_twice) a c' →
    (∀ a' c'', ¬ owned_step c' a' c'') ∧
    (∀ a' c'', ¬ owned_step (project .child c') a' c'') ∧
    isStuck (owned_interp c') := by
  intro H
  obtain ⟨-, ⟨t, rfl, rfl⟩, -⟩ := free_step _ _ _ H
  have Hh := denote_free_head 1
  have Hrun : isStuck (interp_schedule_nd sh 2 #v[denote (.free 1), pure ⟨⟩] (some 0)
      ((hunion freed.1 bP.1, hunion freed.2 bP.2), ([], 0))) := by
    rw [interp_schedule_nd_equ sh 2 _
      (#v[pure ⟨⟩, pure ⟨⟩].set 0 (denote_flow (.free 1) >>= fun _ => pure ⟨⟩)) _ _
      (fun i => by
        match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl)]
    exact isStuck_sbisim (interp_nd_source_free_invalid 1 _ 0 1 _
      (hunion freed.1 bP.1, hunion freed.2 bP.2) [] 0 rfl) stuck_isStuck
  refine ⟨fun a' c'' H' => ?_, fun a' c'' H' => ?_, Hrun⟩
  · rw [owned_step_focus _ 1 _ #v[.child, .parent] 0 _ _ rfl,
      focus_step_head_prim _ 1 _ #v[.child, .parent] 0 _ _ 0 _ _ Hh] at H'
    obtain ⟨k, kind, y, c1, -, Hp, -⟩ := H'
    cases (prim_free_none _ 1 rfl).symm.trans Hp
  · rw [owned_step_focus _ 0 #v[denote (.free 1)] #v[.child] 0 _ _ (by proj_pool),
      focus_step_head_prim _ 0 _ #v[.child] 0 _ _ 0 _ _ Hh] at H'
    obtain ⟨k, kind, y, c1, -, Hp, -⟩ := H'
    cases (prim_free_none _ 1 rfl).symm.trans Hp

/-- `free 0` succeeds and changes neither heap. -/
theorem free_zero_noop :
    hcan_step owned_next (bfocus pfree0) ∧
    ∀ a c', owned_step (bfocus pfree0) a c' →
      a = act .child (.free 0) ∧ ∀ i, c'.heap i = (bfocus pfree0).heap i := by
  refine ⟨⟨_, _, ostep_prim (bfocus pfree0) 1 _ #v[.child, .parent] 0 (.inl (.free 0)) _
    (.free 0) PUnit.unit (set_heap (bfocus pfree0) .child bC) _ rfl (denote_free_head 0) rfl
    rfl⟩, fun a c' H => ?_⟩
  rw [owned_step_focus _ 1 #v[denote pfree0, pure ⟨⟩] #v[.child, .parent] 0 _ _ rfl,
    focus_step_head_prim _ 1 #v[denote pfree0, pure ⟨⟩] #v[.child, .parent] 0 _ _ 0 _ _
      (denote_free_head 0)] at H
  obtain ⟨k, kind, y, c1, -, Hp, rfl, rfl⟩ := H
  change some (OwnedKind.free 0, ⟨⟩, set_heap (bfocus pfree0) .child bC) = some (kind, y, c1)
    at Hp
  simp only [Option.some.injEq, Prod.mk.injEq] at Hp
  obtain ⟨rfl, -, rfl⟩ := Hp
  exact ⟨rfl, fun i => by cases i <;> rfl⟩

/-! ### A foreign read is not confined -/

def pread_foreign : CProg Unit := .bind (.read 2) fun _ => .ret ()

theorem read_foreign_not_confined : ¬ confined bC (project .child (b0 pread_foreign)) := by
  intro Hc
  have Hr : Star owned_next (project .child (b0 pread_foreign))
      (set_pool (project .child (b0 pread_foreign))
        (mk_pool 1 #v[denote pread_foreign] #v[.child] (some 0))) :=
    Star.single ⟨_, ostep_select _ 0 #v[denote pread_foreign] #v[.child] 0
      (by unfold b0 init_owned init_owned_threads; proj_pool)⟩
  exact Hc _ Hr (denote pread_foreign) .child (.inl (.read 2)) (fun _ => denote (.ret ())) rfl
    ⟨0, denote_read_bind 2 _⟩ rfl

theorem read_foreign_not_admissible : ¬ admissible pread_foreign .yield bC bP [] 0 :=
  fun ⟨_, _, _, _, _, Hc, _⟩ => read_foreign_not_confined Hc

/-- Yet cell `2` is present in the joined heap, where the original runner reads `7` and
continues. -/
theorem read_foreign_joined :
    (bC ⊎ bP).1 2 = some 7 ∧
    interp_schedule_nd sh 2 #v[denote pread_foreign, pure ⟨⟩] (some 0) (bC ⊎ bP, ([], 0)) ~
      interp_schedule_nd sh 2 #v[denote (.ret ()), pure ⟨⟩] (some 0) (bC ⊎ bP, ([], 0)) := by
  refine ⟨rfl, ?_⟩
  rw [show denote pread_foreign = _ from
    source_raw_bind (.read 2) (fun _ => .ret ()) fun _ => pure ⟨⟩]
  exact interp_nd_source_read_value 1 #v[pure ⟨⟩, pure ⟨⟩] 0 2 7 _ (hunion bC.1 bP.1)
    (hunion bC.2 bP.2) [] 0 rfl

-- Not ported: `hsingle_disj` (moved to `Tisl.Heap.hsingle_disj`), `denote_read_bind_head`
-- (redundant with `CoCSL.denote_read_bind`). Rocq's `head`/`ostep`/`owned_equ_proj` (Ltac) and
-- `oselect` (Tactic Notation) are the local macros above (plus helper macros `vremove`,
-- `slots_simp`, `proj_pool`).

end Examples.CSL.Frame.Separation.HeapRegression
