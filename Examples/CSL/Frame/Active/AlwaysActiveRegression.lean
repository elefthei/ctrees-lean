/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Separation.AlwaysRegression
public import Lang.CoCSL.Mod
public import Lang.CoCSL.Owned
public import Logic.Sep.Asep
public import Logic.CTree.TraceRules

/-!
# Regression: active separation of two looping lineages

Each lineage of `AlwaysRegression.c0` loops writing its cell, emitting and yielding. Each local
projection always eventually emits its own stamp (`child_local_ag`, `parent_local_ag`, through the
closed-turn invariance rule `ag_csl_nd_invariance`), and `asep_agc_compose` composes the two
local `AG` facts into one global `AG` of the separated assertion (`loops_active_ag`)
(← `examples/CSL/Frame/Active.v`, module `AlwaysActiveRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.AlwaysActiveRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Separation.AlwaysRegression

def initial : AsepState := { cfg := c0, global := .pure, loc := fun _ => .pure }

/-- One turn of the loop: write the held value, emit, and yield back to the loop head. -/
theorem loop_turn (a v tag : Nat) (h : ManagedHeap) (ctx : Ctx) (c : Nat) :
    h.1 a = some v →
    segment_to sh csl_equ (denote (cloop a v tag)) (h, (ctx, c))
      [CSLObs.heap (upd h.1 a v, h.2), CSLObs.emit (stamp (tag, v) c)]
      (denote (cloop a v tag)) ((upd h.1 a v, h.2), (ctx, c + 1)) := by
  intro Hv
  obtain ⟨heap, allocs⟩ := h
  refine ⟨.guard (denote (cloop a v tag)), .equ (cloop_unfold a v tag) ?_ rfl,
    guard_equ_left _ _ (.refl _)⟩
  refine .user (E := sE) (B := Bn) (Sg := SSig) (e := (Sum.inl (HeapOp.write a v) : sE.I))
    (k := fun _ => tE a v tag) (result := PUnit.unit)
    (σ1 := ((upd heap a v, allocs), (ctx, c))) (before := [CSLObs.heap (upd heap a v, allocs)])
    (after := [CSLObs.emit (stamp (tag, v) c)]) _ _ _ ?_ ?_
  · show heap_handlerW CSLObs.heap (.write a v) ((heap, allocs), (ctx, c)) = _
    rw [heap_handlerW_wr_some CSLObs.heap a heap allocs (ctx, c) v v Hv]; rfl
  refine .user (E := sE) (B := Bn) (Sg := SSig) (e := (Sum.inr (Sum.inr (tag, v)) : sE.I))
    (k := fun _ => tY a v tag) (result := PUnit.unit)
    (σ1 := ((upd heap a v, allocs), (ctx, c + 1))) (before := [CSLObs.emit (stamp (tag, v) c)])
    (after := []) _ _ _ rfl ?_
  exact .yield _ _

def loop_inv (a v : Nat) (_ : Unit) (s : SSig) : Prop := (csl_memory s).1 a = some v

private theorem csl_pool_single (p : CProg Unit) : csl_pool #v[p] = #v[denote p] :=
  Vector.ext fun i hi => by match i, hi with | 0, _ => simp [csl_pool]

theorem loop_closed (a v tag : Nat) :
    ClosedTurns sh (csl_pool #v[cloop a v tag]) (loop_inv a v) := by
  intro _ s i Hv
  obtain ⟨h, ctx, c⟩ := s
  obtain rfl := fin1_eq i
  rw [csl_pool_single]
  exact ⟨(), ((upd h.1 a v, h.2), (ctx, c + 1)), _, loop_turn a v tag h ctx c Hv,
    by simp [loop_inv, csl_memory, upd]⟩

theorem loop_af_focused (a v tag : Nat) (s : SSig) (w : World (writerE (CSLObs (Nat × Nat)))) :
    loop_inv a v () s → NotDone w →
    entails (AF (visWₜ (csl_indexed fun e => e.value = (tag, v))))
      (run_nd_pool #v[cloop a v tag] (some 0) s) w := by
  obtain ⟨h, ctx, c⟩ := s
  intro Hv Hw
  have Ht := loop_turn a v tag h ctx c Hv
  rw [← show (csl_pool #v[cloop a v tag])[(0 : Fin 1)] = denote (cloop a v tag) by
    rw [csl_pool_single]; rfl] at Ht
  refine (proper_entails_meq _ (run_nd_pool_turn #v[cloop a v tag] 0 _ _ _ Ht)).2 ?_
  exact af_emit_list_member _ _ _ _ (CSLObs.emit (stamp (tag, v) c)) Hw (by simp) rfl

theorem loop_af (a v tag : Nat) (s : SSig) (focus : Option (Fin 1))
    (w : World (writerE (CSLObs (Nat × Nat)))) :
    loop_inv a v () s → NotDone w →
    entails (AF (visWₜ (csl_indexed fun e => e.value = (tag, v))))
      (run_nd_pool #v[cloop a v tag] focus s) w := by
  intro Hv Hw
  cases focus with
  | some i => obtain rfl := fin1_eq i; exact loop_af_focused a v tag s w Hv Hw
  | none =>
    refine (proper_entails_meq _ (run_nd_pool_select _ s)).2 ?_
    refine (au_brS (B := Bn) (c := ⟨0 + 1⟩) ⟨0⟩).1 (.inr ⟨⟨trivial, Hw⟩, fun j => ?_⟩)
    refine (fun i => ?_ : ∀ i : Fin 1, entails _ (run_nd_pool _ (some i) s) w) _
    obtain rfl := fin1_eq i
    exact loop_af_focused a v tag s w Hv Hw

theorem loop_agaf (a v tag : Nat) (s : SSig) (focus : Option (Fin 1))
    (w : World (writerE (CSLObs (Nat × Nat)))) :
    loop_inv a v () s → NotDone w →
    entails (AG (AF (visWₜ (csl_indexed fun e => e.value = (tag, v)))))
      (run_nd_pool #v[cloop a v tag] focus s) w := by
  intro Hv Hw
  refine ag_csl_nd_invariance #v[cloop a v tag] (loop_inv a v)
    (AF (visWₜ (csl_indexed fun e => e.value = (tag, v)))) (loop_closed a v tag) ?_
    (fun _ _ f z Hinv Hz => loop_af a v tag _ f z Hinv Hz) () s focus w Hv Hw
  intro o t z Hz Hphi
  have Hlog := af_log (k := t) (s := o) Hz Hphi
  simp only [log, vis_bind, pure_bind'] at Hlog
  exact Hlog

def child_obligation : TiclAt (writerE (CSLObs (Nat × Nat))) (Unit × SSig) false :=
  AF (visWₜ (csl_indexed fun e => e.value = (1, 1)))

def parent_obligation : TiclAt (writerE (CSLObs (Nat × Nat))) (Unit × SSig) false :=
  AF (visWₜ (csl_indexed fun e => e.value = (0, 8)))

def child_pred : ctreeW (CSLObs (Nat × Nat)) Bn (Unit × SSig) →
    World (writerE (CSLObs (Nat × Nat))) → Prop :=
  entails child_obligation

def parent_pred : ctreeW (CSLObs (Nat × Nat)) Bn (Unit × SSig) →
    World (writerE (CSLObs (Nat × Nat))) → Prop :=
  entails parent_obligation

theorem child_local_ag : agc child_pred (owned_interp (project .child c0)) .pure := by
  unfold c0
  rw [owned_equ_eq (project_init_child pc pp hC hP ctx0 0)]
  show entails (AG child_obligation) (interp_schedule_nd sh 1 #v[denote pc] none _) .pure
  rw [← csl_pool_single]
  exact loop_agaf 1 1 1 _ none .pure rfl .pure

theorem parent_local_ag : agc parent_pred (owned_interp (project .parent c0)) .pure := by
  unfold c0
  rw [owned_equ_eq (project_init_parent pc pp hC hP ctx0 0)]
  show entails (AG parent_obligation) (interp_schedule_nd sh 1 #v[denote pp] (some 0) _) .pure
  rw [← csl_pool_single]
  exact loop_agaf 2 8 0 _ (some 0) .pure rfl .pure

theorem initial_ok : asep_state_ok initial :=
  ⟨admissible_active_erasable _ _ _ _ _ _ loops_admissible, .pure, fun _ => .pure⟩

/-- Both looping lineages always eventually emit, composed through active separation. -/
theorem loops_active_ag :
    agc (asep_sat (fun _ => True) child_pred parent_pred) (owned_interp c0) .pure :=
  asep_agc_compose _ _ _ _ _ asep_closed_true (asep_pred_ok_entails _) (asep_pred_ok_entails _)
    (asep_sat_intro _ _ _ initial
      (asep_at_intro _ _ _ _ initial_ok trivial child_local_ag parent_local_ag))

end Examples.CSL.Frame.Active.AlwaysActiveRegression
