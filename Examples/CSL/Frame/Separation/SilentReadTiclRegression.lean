/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Asep
public import Logic.CTree.AG

/-!
# Silent reads: owned `AG` without visible progress

A source loop that only reads its own cell runs forever in the owned machine, yet every read is
erased, so the erased runner and the original fork are stuck and satisfy no `AG`; the infinite
owned run selects infinitely many reads but only finitely many visible actions
(← `examples/CSL/Frame/Separation.v`, module `SilentReadTiclRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation.SilentReadTiclRegression
open CTree Tisl Tisl.CSL Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield Tisl.Notation CoCSL

def read_loop : CProg Unit :=
  .untilNone (.bind (.read 2) fun _ => .ret (some () : Option Unit))
def read_heap : ManagedHeap := (hsingle 2 8, hemp)
def read_initial : OwnedCfg := init_owned (.ret ()) read_loop managed_empty read_heap [] 0
def read_alone : OwnedCfg := init_local .parent read_loop read_heap [] 0 true
def read_head : Thread sE Bn :=
  .vis (E := CEff) (.inr (.inr (.inl (.read 2)))) fun _ => .guard (denote read_loop)

theorem read_loop_unfold : denote read_loop = read_head := by
  show denote_flow read_loop >>= _ = _
  rw [read_loop, source_raw_until, source_raw_bind, source_raw_read_head]
  simp only [source_raw_ret]
  rfl

theorem read_admissible : admissible (.ret ()) read_loop managed_empty read_heap [] 0 :=
  admissible_intro _ _ _ _ _ _ managed_wf_empty (managed_wf_preallocated _)
    ⟨fun _ => .inl rfl, fun _ => .inl rfl⟩ trivial ⟨trivial, fun _ => trivial⟩ trivial
    ⟨by simp [addr_ok, read_heap, hsingle], fun _ => trivial⟩

/-- A successful read retains focus, heap, counter and observations; the continuation is a guard
back to the same source loop. -/
def read_Inv (d : OwnedCfg) : Prop :=
  (d.heap .parent).1 2 = some 8 ∧
  ∃ (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1)) (j : Fin (n + 1)),
    d.pool = mk_pool (n + 1) v g (some j) ∧ g[j] = .parent ∧
    ∃ m, v[j] = guards m read_head

theorem read_initial_Inv : read_Inv read_initial :=
  ⟨rfl, 1, #v[denote (.ret ()), denote read_loop], #v[.child, .parent], 1, rfl, rfl, 0,
    read_loop_unfold⟩

theorem read_alone_Inv : read_Inv read_alone :=
  ⟨rfl, 0, #v[denote read_loop], #v[.parent], 0, rfl, rfl, 0, read_loop_unfold⟩

theorem read_Inv_step (d : OwnedCfg) (a : OwnedAction) (d' : OwnedCfg) :
    read_Inv d → owned_step d a d' → a = act .parent .read ∧ read_Inv d' := by
  rintro ⟨Hcell, n, v, g, j, Hpool, Hg, m, Hm⟩ Hs
  unfold owned_step at Hs
  rw [Hpool] at Hs
  change focus_step d n v g j a d' at Hs
  rw [focus_step_head_prim d n v g j _ _ m a d' Hm] at Hs
  obtain ⟨k, kind, y, c1, Hk, Hprim, rfl, rfl⟩ := Hs
  rw [Hg] at Hprim
  simp only [prim_step, heap_prim, Hcell, Option.some.injEq, Prod.mk.injEq] at Hprim
  obtain ⟨rfl, rfl, rfl⟩ := Hprim
  refine ⟨by rw [Hg], Hcell, n, v.set j (k (8 : Nat)), g, j, rfl, Hg, 1, ?_⟩
  rw [Fin.getElem_fin, Vector.getElem_set_self, Hk, guards_succ, guards_zero]
  show CTree.guard (denote read_loop) = _
  rw [read_loop_unfold]

theorem read_Inv_can (d : OwnedCfg) : read_Inv d → ∃ d', owned_step d (act .parent .read) d' := by
  rintro ⟨Hcell, n, v, g, j, Hpool, Hg, m, Hm⟩
  refine ⟨set_pool d (mk_pool (n + 1) (v.set j (.guard (denote read_loop))) g (some j)), ?_⟩
  unfold owned_step
  rw [Hpool]
  show focus_step d n v g j _ _
  refine (focus_step_head_prim d n v g j _ _ m _ _ Hm).2
    ⟨fun _ => .guard (denote read_loop), .read, (8 : Nat), d, fun _ => rfl, ?_, by rw [Hg], rfl⟩
  rw [Hg]
  simp only [prim_step, heap_prim, Hcell]

theorem read_infinite_owned (c : OwnedCfg) : read_Inv c → hAG owned_next hTrue c :=
  hAG_coind _ _ read_Inv (fun d HI =>
    ⟨trivial, (read_Inv_can d HI).elim fun d' Hs => ⟨d', _, Hs⟩,
      fun d' ⟨a, Hs⟩ => (read_Inv_step d a d' HI Hs).2⟩) c

theorem read_loop_owned_hag : hAG owned_next hTrue read_initial :=
  read_infinite_owned _ read_initial_Inv

theorem read_loop_focused_owned_hag : hAG owned_next hTrue read_alone :=
  read_infinite_owned _ read_alone_Inv

theorem read_loop_projection : owned_equ (project .parent read_initial) read_alone :=
  project_init_parent _ _ _ _ _ _

theorem read_Inv_silent_reach (c d : OwnedCfg) :
    read_Inv c → Star silent_next c d → read_Inv d :=
  clos_refl_trans_preserves _ _ (fun x y Hx ⟨a, Hs, _⟩ => (read_Inv_step x a y Hx Hs).2) c d

theorem read_Inv_nonterminal (d : OwnedCfg) : read_Inv d → d.pool.size ≠ 0 := by
  rintro ⟨-, n, v, g, j, Hp, -⟩
  rw [Hp]
  exact Nat.succ_ne_zero n

theorem read_loop_erasure_stuck : isStuck (owned_interp read_initial) := by
  intro l T Ht
  obtain ⟨d, Hd, ⟨a, d', Hs, Hl, -⟩ | ⟨Hz, -⟩⟩ := owned_interp_trans_forward read_initial l T
    (admissible_erasable _ _ _ _ _ _ read_admissible) Ht
  · obtain ⟨rfl, -⟩ := read_Inv_step d a d' (read_Inv_silent_reach _ _ read_initial_Inv Hd) Hs
    cases Hl
  · exact read_Inv_nonterminal d (read_Inv_silent_reach _ _ read_initial_Inv Hd) Hz

theorem read_loop_erasure_no_ag : ¬ entails (AG ⊤) (owned_interp read_initial) .pure := by
  intro H
  obtain ⟨T, w, Ht⟩ := (agc_unfold.1 H).2.1
  obtain ⟨l, Ht, -⟩ := ktrans_trans.1 Ht
  exact read_loop_erasure_stuck l T Ht

theorem read_loop_original_stuck :
    isStuck (run_nd (.bind (.fork (.ret ())) fun _ => read_loop)
      (managed_empty ⊎ read_heap, ([], 0))) :=
  isStuck_sbisim (sbisim_symm (owned_fork_runner (.ret ()) (fun _ => read_loop) managed_empty
    read_heap [] 0)) read_loop_erasure_stuck

theorem read_loop_original_no_ag :
    ¬ entails (AG ⊤) (run_nd (.bind (.fork (.ret ())) fun _ => read_loop)
      (managed_empty ⊎ read_heap, ([], 0))) .pure := by
  intro H
  obtain ⟨T, w, Ht⟩ := (agc_unfold.1 H).2.1
  obtain ⟨l, Ht, -⟩ := ktrans_trans.1 Ht
  exact read_loop_original_stuck l T Ht

def read_again : OwnedCfg :=
  set_pool read_initial
    (mk_pool 2 #v[denote (.ret ()), .guard (denote read_loop)] #v[.child, .parent] (some 1))

theorem read_first_step : owned_step read_initial (act .parent .read) read_again := by
  show focus_step read_initial 1 #v[denote (.ret ()), denote read_loop] #v[.child, .parent] 1
    (act .parent .read) read_again
  exact (focus_step_head_prim read_initial 1 #v[denote (.ret ()), denote read_loop]
    #v[.child, .parent] 1 _ _ 0 _ _ read_loop_unfold).2
    ⟨fun _ => .guard (denote read_loop), .read, (8 : Nat), read_initial, fun _ => rfl, rfl, rfl,
      rfl⟩

theorem read_again_step : owned_step read_again (act .parent .read) read_again := by
  show focus_step read_again 1 #v[denote (.ret ()), .guard (denote read_loop)]
    #v[.child, .parent] 1 (act .parent .read) read_again
  have H : CTree.guard (denote read_loop) = guards 1 read_head := by rw [read_loop_unfold]; rfl
  exact (focus_step_head_prim read_again 1 #v[denote (.ret ()), .guard (denote read_loop)]
    #v[.child, .parent] 1 _ _ 1 _ _ H).2
    ⟨fun _ => .guard (denote read_loop), .read, (8 : Nat), read_again, fun _ => rfl, rfl, rfl,
      rfl⟩

def read_forever : Execution OwnedCfg OwnedAction Unit where
  states := fun | 0 => read_initial | _ + 1 => read_again
  selected := fun _ => act .parent .read
  emitted := fun _ => ()

theorem read_forever_run : read_forever.states 0 = read_initial ∧ owned_run read_forever :=
  ⟨rfl, fun | 0 => read_first_step | _ + 1 => read_again_step⟩

theorem read_forever_infinitely_reads :
    infinitely (fun n => read_forever.selected n = act .parent .read) :=
  fun n => ⟨n, Nat.le_refl n, rfl⟩

theorem read_forever_not_infinitely_visible :
    ¬ infinitely (fun n => erase_action_label (read_forever.selected n)
      (joined_heap (read_forever.states (n + 1))) ≠ none) :=
  fun H => let ⟨_, _, Hn⟩ := H 0; Hn rfl

end Examples.CSL.Frame.Separation.SilentReadTiclRegression
