/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Surface
public import Logic.Sep.Frame
public import Logic.Yield.Frame

/-!
# Heap frame rules for CoCSL source programs

The same program runs on a heap extended by a disjoint `ManagedHeap`. All atoms acquire their
`framer` image; native postconditions acquire `frame_post`. Unconditional admission excludes
allocation; a conditional allocation rule requires a common first fit and the full allocated
managed-state relation (← `Lang/CoCSL/Frame.v`).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx Tisl.Pcm
open ITree (Effect)

/-- `okE` admits every event the expression can trigger. -/
def exp_ok (okE : CEff.I → Prop) : CExp → Prop
  | .var _ => okE (.inr (.inr (.inr (.inl .get)))) ∧ okE (.inl ⟨⟩)
  | .lit _ => True
  | .plus a b | .minus a b | .mult a b => exp_ok okE a ∧ exp_ok okE b

/-- `okE` admits every event the program can trigger. -/
def prog_ok (okE : CEff.I → Prop) : {A : Type} → CProg A → Prop
  | _, .read a => okE (.inr (.inr (.inl (.read a))))
  | _, .write a v => okE (.inr (.inr (.inl (.write a v))))
  | _, .emit tag v => okE (.inr (.inr (.inr (.inr (tag, v)))))
  | _, .yield => okE (.inl ⟨⟩)
  | _, .fork body => okE (.inr (.inl ⟨⟩)) ∧ prog_ok okE body
  | _, .ret _ => True
  | _, .bind body next => prog_ok okE body ∧ ∀ a, prog_ok okE (next a)
  | _, .untilNone body => prog_ok okE body
  | _, .alloc size => okE (.inr (.inr (.inl (.alloc size))))
  | _, .free base => okE (.inr (.inr (.inl (.free base))))
  | _, .cas a expected desired =>
    exp_ok okE a ∧ exp_ok okE expected ∧ exp_ok okE desired ∧
      ∀ addr old value, okE (.inr (.inr (.inl (.cas addr old value))))
  | _, .eval e => exp_ok okE e
  | _, .assign _ e =>
    exp_ok okE e ∧ okE (.inr (.inr (.inr (.inl .get)))) ∧
      ∀ ctx, okE (.inr (.inr (.inr (.inl (.put ctx)))))
  | _, .ite e yes no => exp_ok okE e ∧ prog_ok okE yes ∧ prog_ok okE no
  | _, .while e body => exp_ok okE e ∧ prog_ok okE body

/-- No allocation: first-fit allocation is deterministic in the absolute heap. -/
def alloc_free {A : Type} (p : CProg A) : Prop := prog_ok (okE_thread no_alloc_sE) p

/-- An admitted heap event followed by framable continuations is framable. -/
theorem fr_heap {X : Type} (okE : CEff.I → Prop) (e : HeapOp)
    (he : okE (.inr (.inr (.inl e)))) (k : heapE.O e → CTree CEff Bn X)
    (hk : ∀ x, Framable okE (k x)) : Framable okE (CTree.trigger' heapE e >>= k) := by
  simp only [CTree.trigger', CTree.vis', vis_bind, pure_bind']
  exact fr_vis okE _ _ he hk

/-- An admitted event followed by framable continuations is framable. -/
theorem fr_trig {X : Type} (okE : CEff.I → Prop) (e : CEff.I) (he : okE e)
    (k : CEff.O e → CTree CEff Bn X) (hk : ∀ x, Framable okE (k x)) :
    Framable okE (CTree.trigger e >>= k) := by
  simp only [CTree.trigger, vis_bind, pure_bind']
  exact fr_vis okE _ _ he hk

/-- Admissible expressions denote framable trees. -/
theorem denote_exp_framable (okE : CEff.I → Prop) (e : CExp) :
    exp_ok okE e → Framable okE (denote_exp e) := by
  induction e with
  | var name =>
    rintro ⟨HG, HY⟩
    refine fr_trig okE _ HG _ fun ctx => ?_
    cases Ctx.lookup name ctx with
    | some v => exact fr_trig okE _ HY _ fun _ => fr_ret okE _
    | none => exact fr_stuck okE
  | lit n => exact fun _ => fr_ret okE n
  | plus a b iha ihb | minus a b iha ihb | mult a b iha ihb =>
    rintro ⟨Ha, Hb⟩
    exact framable_bind okE _ _ (iha Ha) fun _ =>
      framable_bind okE _ _ (ihb Hb) fun _ => fr_ret okE _

/-- The shared admissibility walk certifies framability of every program constructor. -/
theorem denote_flow_framable (okE : CEff.I → Prop) {A : Type} (p : CProg A) :
    prog_ok okE p → Framable okE (denote_flow p) := by
  induction p with
  | read a | write a v | alloc size | free base =>
    exact fun Hp => fr_heap okE _ Hp _ fun _ => fr_ret okE _
  | emit q v | yield => exact fun Hp => fr_trig okE _ Hp _ fun _ => fr_ret okE _
  | fork body ih =>
    rintro ⟨HF, Hb⟩
    refine fr_trig okE _ HF _ fun child => ?_
    cases child
    · exact fr_ret okE _
    · exact framable_bind okE _ _ (ih Hb) fun _ => fr_ret okE _
  | ret x => exact fun _ => fr_ret okE _
  | bind body next ih ihn =>
    rintro ⟨Hb, Hn⟩
    rw [denote_flow]
    refine framable_bind okE _ _ (ih Hb) fun flow => ?_
    cases flow
    · exact fr_ret okE _
    · exact ihn _ (Hn _)
  | untilNone body ih =>
    intro Hp
    refine framable_iter okE _ (fun _ => framable_bind okE _ _ (ih Hp) fun flow => ?_) _
    rcases flow with _ | _ | _ <;> exact fr_ret okE _
  | cas a expected desired =>
    rintro ⟨Ha, He, Hd, HC⟩
    exact framable_bind okE _ _ (denote_exp_framable okE a Ha) fun addr =>
      framable_bind okE _ _ (denote_exp_framable okE expected He) fun old =>
      framable_bind okE _ _ (denote_exp_framable okE desired Hd) fun value =>
      fr_heap okE _ (HC addr old value) _ fun _ => fr_ret okE _
  | eval e =>
    intro Hp
    exact framable_bind okE _ _ (denote_exp_framable okE e Hp) fun _ => fr_ret okE _
  | assign name e =>
    rintro ⟨He, HG, HP⟩
    exact framable_bind okE _ _ (denote_exp_framable okE e He) fun v =>
      fr_trig okE _ HG _ fun ctx => fr_trig okE _ (HP (Ctx.add name v ctx)) _ fun _ =>
        fr_ret okE _
  | ite test yes no ihy ihn =>
    rintro ⟨He, Hy, Hn⟩
    refine framable_bind okE _ _ (denote_exp_framable okE test He) fun v => ?_
    cases is_true v
    · exact ihn Hn
    · exact ihy Hy
  | «while» test body ih =>
    rintro ⟨He, Hb⟩
    refine framable_iter okE _ (fun _ =>
      framable_bind okE _ _ (denote_exp_framable okE test He) fun v => ?_) _
    cases is_true v
    · exact fr_ret okE _
    · exact framable_bind okE _ _ (ih Hb) fun flow => by cases flow <;> exact fr_ret okE _

/-- Allocation-free programs denote framable complete threads. -/
theorem denote_framable (p : CProg Unit) :
    alloc_free p → Framable (okE_thread no_alloc_sE) (denote p) := fun Hp =>
  framable_bind _ _ _ (denote_flow_framable _ p Hp) fun _ => fr_ret _ _

/-- Source denotations form a branch-free scheduler pool. -/
theorem csl_pool_branchfree {n : Nat} (ps : Vector (CProg Unit) n) :
    pool_branchfree (csl_pool ps) := fun i => by
  simp only [csl_pool, Fin.getElem_fin, Vector.getElem_map]; exact denote_branchfree _

/-- An allocation-free source pool is framable. -/
theorem csl_pool_framable {n : Nat} (ps : Vector (CProg Unit) n) :
    (∀ i : Fin n, alloc_free ps[i]) → pool_framable no_alloc_sE (csl_pool ps) := fun Hps i => by
  simp only [csl_pool, Fin.getElem_fin, Vector.getElem_map]; exact denote_framable _ (Hps i)

/-! ## Framability of each runner's erased tree -/

/-- The erased nondeterministic pool runner is framable. -/
theorem run_nd_pool_framable {n : Nat} (ps : Vector (CProg Unit) n) (focus : Option (Fin n)) :
    (∀ i : Fin n, alloc_free ps[i]) →
    Framable no_alloc_sE (project_scheduled (schedule n (csl_pool ps) focus)) := fun H =>
  framable_erased_nd _ n _ focus (csl_pool_branchfree ps) (csl_pool_framable ps H)

/-- The round-robin scheduled pool is framable: scheduling events are always admitted. -/
theorem run_rr_pool_framable {n : Nat} (ps : Vector (CProg Unit) n) (focus : Option (Fin n))
    (cursor : Nat) : (∀ i : Fin n, alloc_free ps[i]) →
    Framable (okE_policy no_alloc_sE) (schedule_policy rr_scheduler n (csl_pool ps) focus cursor) :=
  fun H => framable_schedule_rr _ n _ focus cursor (csl_pool_branchfree ps) (csl_pool_framable ps H)

/-- The standalone erased flow of an allocation-free program is framable. -/
theorem instr_flow_framable {A : Type} (p : CProg A) :
    alloc_free p → Framable no_alloc_sE (interp_thread (denote_flow p)) := fun H =>
  framable_thread _ _ (denote_flow_framable _ p H)

/-- The singleton nondeterministic runner has a framable erased tree. -/
theorem run_nd_framable (p : CProg Unit) : alloc_free p →
    Framable no_alloc_sE (project_scheduled (schedule 1 (csl_pool #v[p]) (some 0))) := fun H =>
  run_nd_pool_framable _ _ fun i => by rw [fin1_eq i]; exact H

/-- The singleton round-robin runner has a framable scheduled tree. -/
theorem run_rr_framable (p : CProg Unit) : alloc_free p →
    Framable (okE_policy no_alloc_sE)
      (schedule_policy rr_scheduler 1 (csl_pool #v[p]) (some 0) (0 : Nat)) := fun H =>
  run_rr_pool_framable _ _ _ fun i => by rw [fin1_eq i]; exact H

/-- Standalone source flow embedded under the instrumented policy handler. -/
theorem instr_flow_sched_framable {A : Type} (p : CProg A) :
    alloc_free p →
    Framable (okE_policy no_alloc_sE)
      (translate (fun e => (⟨.inl e, id⟩ : (f : (sE ⊕ₑ schedE).I) × ((sE ⊕ₑ schedE).O f → sE.O e)))
        (interp_thread (denote_flow p))) := fun H =>
  framable_translate_inl1 _ _ (instr_flow_framable p H)

/-! ## All-atom framing for the existing source execution shapes -/

theorem instr_exp_csl_frame {b : Bool} (fr : ManagedHeap) (e : CExp) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat))) (Nat × SSig) b) (w w' : World _) :
    exp_ok (okE_thread no_alloc_sE) e → frame_rel fr s s' →
    simW (frameER fr) (frameRV (X := Nat) fr) w w' →
    entails p (instr_exp_erased e s) w →
    entails (framer (Nat × SSig) b (frameER fr) (frameRV fr) p) (instr_exp_erased e s') w' :=
  fun HF HR HW H => ticl_csl_frame fr _ s s'
    (framable_thread _ _ (denote_exp_framable _ e HF)) HR p w w' HW H

theorem instr_flow_csl_frame {A : Type} {b : Bool} (fr : ManagedHeap) (source : CProg A)
    (s s' : SSig) (p : TiclAt (writerE (CSLObs (Nat × Nat))) (Option A × SSig) b)
    (w w' : World _) :
    alloc_free source → frame_rel fr s s' →
    simW (frameER fr) (frameRV (X := Option A) fr) w w' →
    entails p (instr_flow_erased source s) w →
    entails (framer (Option A × SSig) b (frameER fr) (frameRV fr) p)
      (instr_flow_erased source s') w' :=
  fun HF HR HW H => ticl_csl_frame fr _ s s' (instr_flow_framable source HF) HR p w w' HW H

theorem run_nd_pool_csl_frame {n : Nat} {b : Bool} (fr : ManagedHeap)
    (ps : Vector (CProg Unit) n) (focus : Option (Fin n)) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat))) (PUnit × SSig) b) (w w' : World _) :
    (∀ i : Fin n, alloc_free ps[i]) → frame_rel fr s s' →
    simW (frameER fr) (frameRV (X := PUnit) fr) w w' →
    entails p (run_nd_pool ps focus s) w →
    entails (framer (PUnit × SSig) b (frameER fr) (frameRV fr) p) (run_nd_pool ps focus s') w' :=
  fun HF HR HW H => ticl_csl_frame fr _ s s' (run_nd_pool_framable ps focus HF) HR p w w' HW H

theorem run_rr_pool_csl_frame {n : Nat} {b : Bool} (fr : ManagedHeap)
    (ps : Vector (CProg Unit) n) (focus : Option (Fin n)) (cursor : Nat) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat) ⊕ Nat)) (PUnit × SSig) b) (w w' : World _) :
    (∀ i : Fin n, alloc_free ps[i]) → frame_rel fr s s' →
    simW (frameERW fr) (frameRV (X := PUnit) fr) w w' →
    entails p (run_rr_pool ps focus cursor s) w →
    entails (framer (PUnit × SSig) b (frameERW fr) (frameRV fr) p)
      (run_rr_pool ps focus cursor s') w' :=
  fun HF HR HW H =>
    ticl_csl_frameW fr _ s s' (run_rr_pool_framable ps focus cursor HF) HR p w w' HW H

theorem run_nd_csl_frame {b : Bool} (fr : ManagedHeap) (source : CProg Unit) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat))) (PUnit × SSig) b) (w w' : World _) :
    alloc_free source → frame_rel fr s s' →
    simW (frameER fr) (frameRV (X := PUnit) fr) w w' →
    entails p (run_nd source s) w →
    entails (framer (PUnit × SSig) b (frameER fr) (frameRV fr) p) (run_nd source s') w' :=
  fun HF HR HW H => ticl_csl_frame fr _ s s' (run_nd_framable source HF) HR p w w' HW H

theorem run_rr_csl_frame {b : Bool} (fr : ManagedHeap) (source : CProg Unit) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat) ⊕ Nat)) (PUnit × SSig) b) (w w' : World _) :
    alloc_free source → frame_rel fr s s' →
    simW (frameERW fr) (frameRV (X := PUnit) fr) w w' →
    entails p (run_rr source s) w →
    entails (framer (PUnit × SSig) b (frameERW fr) (frameRV fr) p) (run_rr source s') w' :=
  fun HF HR HW H => ticl_csl_frameW fr _ s s' (run_rr_framable source HF) HR p w w' HW H

/-- A scheduled allocation may frame only when both heaps select the same first-fit block and the
full allocated memories remain frame-related. -/
theorem ticl_csl_nd_alloc_frame_at {b : Bool} (fr : ManagedHeap) (n : Nat)
    (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size base : Nat)
    (K : Option Nat → Thread sE Bn) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat))) (PUnit × SSig) b) (w w' : World _) :
    frame_rel fr s s' → 0 < size → 0 < base →
    block_free (csl_memory s).1 base size →
    block_free (csl_memory s').1 base size →
    (∀ j, 0 < j → j < base → ¬ block_free (csl_memory s).1 j size) →
    (∀ j, 0 < j → j < base → ¬ block_free (csl_memory s').1 j size) →
    frame_rel fr (managed_alloc (csl_memory s) base size, s.2)
      (managed_alloc (csl_memory s') base size, s'.2) →
    Framable no_alloc_sE
      (project_scheduled (schedule (n + 1) (ts.set i (K (some base))) (some i))) →
    simW (frameER fr) (frameRV (X := PUnit) fr) w w' →
    entails p
      (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) s) w →
    entails (framer (PUnit × SSig) b (frameER fr) (frameRV fr) p)
      (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i) s')
      w' := by
  intro _ Hsize Hbase Hfree Hfree' Hfirst Hfirst' Hpost HF HW H
  obtain ⟨⟨h, allocs⟩, ctx, c⟩ := s
  obtain ⟨⟨h', allocs'⟩, ctx', c'⟩ := s'
  have H := (proper_entails_meq p (interp_nd_source_alloc_first n ts i size base K h allocs ctx c
    Hsize Hbase Hfree Hfirst)).1 H
  refine (proper_entails_meq _ (interp_nd_source_alloc_first n ts i size base K h' allocs' ctx' c'
    Hsize Hbase Hfree' Hfirst')).2 ?_
  exact ticl_csl_frame_log fr _ _ _ _ _ p w w' HF Hpost (frameER_heap fr _ _ Hpost) HW H

theorem ticl_csl_rr_alloc_frame_at {b : Bool} (fr : ManagedHeap) (n : Nat)
    (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size base : Nat)
    (K : Option Nat → Thread sE Bn) (cursor : Nat) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat) ⊕ Nat)) (PUnit × SSig) b) (w w' : World _) :
    frame_rel fr s s' → 0 < size → 0 < base →
    block_free (csl_memory s).1 base size →
    block_free (csl_memory s').1 base size →
    (∀ j, 0 < j → j < base → ¬ block_free (csl_memory s).1 j size) →
    (∀ j, 0 < j → j < base → ¬ block_free (csl_memory s').1 j size) →
    frame_rel fr (managed_alloc (csl_memory s) base size, s.2)
      (managed_alloc (csl_memory s') base size, s'.2) →
    Framable (okE_policy no_alloc_sE)
      (schedule_policy rr_scheduler (n + 1) (ts.set i (K (some base))) (some i) cursor) →
    simW (frameERW fr) (frameRV (X := PUnit) fr) w w' →
    entails p (interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
      (some i) cursor s) w →
    entails (framer (PUnit × SSig) b (frameERW fr) (frameRV fr) p)
      (interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i)
        cursor s') w' := by
  intro _ Hsize Hbase Hfree Hfree' Hfirst Hfirst' Hpost HF HW H
  obtain ⟨⟨h, allocs⟩, ctx, c⟩ := s
  obtain ⟨⟨h', allocs'⟩, ctx', c'⟩ := s'
  have H := (proper_entails_meq p (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c
    Hsize Hbase Hfree Hfirst)).1 H
  refine (proper_entails_meq _ (interp_rr_alloc_first n ts i size base K cursor h' allocs' ctx'
    c' Hsize Hbase Hfree' Hfirst')).2 ?_
  exact ticl_csl_frameW_log fr _ _ _ _ _ p w w' HF Hpost (frameERW_heap fr _ _ Hpost) HW H

/-- Client-facing unfolding of a framed postcondition on the memory component. -/
theorem frame_post_iff {X : Type} (fr : ManagedHeap)
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (M : ManagedHeap)
    (aux : Ctx × Nat) (x : X) (w' : World (writerE (CSLObs (Nat × Nat)))) :
    frame_post fr P (x, (M, aux)) w' ↔
      ∃ m w, m # fr ∧ managed_wf m ∧ M ≈ m ⊎ fr ∧
        simW (frameER fr) (frameRV (X := X) fr) w w' ∧ P (x, (m, aux)) w := by
  constructor
  · rintro ⟨⟨x', m, aux'⟩, w, ⟨rfl, ⟨HD, HW⟩, rfl, HE⟩, Hworld, HP⟩
    exact ⟨m, w, HD, HW, HE, Hworld, HP⟩
  · rintro ⟨m, w, HD, HW, HE, Hworld, HP⟩
    exact ⟨(x, (m, aux)), w, ⟨rfl, ⟨HD, HW⟩, rfl, HE⟩, Hworld, HP⟩

/-- Logged postconditions preserve both framed memory and predecessor worlds. -/
theorem frame_postW_iff {X : Type} (fr : ManagedHeap)
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop) (M : ManagedHeap)
    (aux : Ctx × Nat) (x : X) (w' : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    frame_postW fr P (x, (M, aux)) w' ↔
      ∃ m w, m # fr ∧ managed_wf m ∧ M ≈ m ⊎ fr ∧
        simW (frameERW fr) (frameRV (X := X) fr) w w' ∧ P (x, (m, aux)) w := by
  constructor
  · rintro ⟨⟨x', m, aux'⟩, w, ⟨rfl, ⟨HD, HW⟩, rfl, HE⟩, Hworld, HP⟩
    exact ⟨m, w, HD, HW, HE, Hworld, HP⟩
  · rintro ⟨m, w, HD, HW, HE, Hworld, HP⟩
    exact ⟨(x, (m, aux)), w, ⟨rfl, ⟨HD, HW⟩, rfl, HE⟩, Hworld, HP⟩

-- Not ported: the `fr_trigger` Ltac (replaced by the private lemmas `fr_heap`, `fr_trig`).

end CoCSL
