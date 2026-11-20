/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.CSL
public import Logic.Yield.Frame
public import Logic.CTree.Sim
public import Logic.Simulation
public import Logic.Congruence

/-!
# Passive framing of the CSL handler

A handler frames when, on admissible events and frame-related states, its responses are stuck,
related returns, or related logs followed by related returns (`FrameHandler`). Interpreting a
framable source in frame-related states then gives a conditional simulation (`csim_interp_frame`),
which transports every TICL formula along `framer` (`ticl_interp_frame`). The CSL handler `sh`
frames for every event except deterministic first-fit allocation (`no_alloc_sE`); a single
allocation frames when both heaps share the first-fit witness (`ticl_csl_alloc_frame_at`)
(← `CTree/Interp/CSL/Frame.v`).
-/

@[expose] public section
namespace Tisl.CSL
open CTree Coinduction Notation Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield
open ITree (Effect)

/-! ## Frame relations -/

/-- Admit all state events except deterministic absolute-heap allocation. -/
def no_alloc_sE : sE.I → Prop
  | .inl (.alloc _) => False
  | _ => True

/-- Add a managed heap frame without changing auxiliary state. -/
def frame_state (fr : ManagedHeap) (s : SSig) : SSig := (csl_memory s ⊎ fr, s.2)

/-- The source owns a well-formed heap disjoint from the frame. -/
def frame_inv (fr : ManagedHeap) (s : SSig) : Prop :=
  csl_memory s # fr ∧ managed_wf (csl_memory s)

/-- The target adds disjoint `fr` up to `≈`, with equal auxiliary state. -/
def frame_rel (fr : ManagedHeap) (s s' : SSig) : Prop :=
  frame_inv fr s ∧ s'.2 = s.2 ∧ csl_memory s' ≈ csl_memory s ⊎ fr

/-- Frame-related results carry equal values and frame-related states. -/
def frameRV {X : Type} (fr : ManagedHeap) : X × SSig → X × SSig → Prop :=
  fun r r' => r'.1 = r.1 ∧ frame_rel fr r.2 r'.2

/-- Observation transport adds the passive frame only to heap snapshots. -/
def frameER {A : Type} (fr : ManagedHeap) : event_rel (writerE (CSLObs A)) :=
  fun (o o' : CSLObs A) =>
    match o, o' with
    | .heap m, .heap m' => m # fr ∧ managed_wf m ∧ m' ≈ m ⊎ fr
    | .ctx c, .ctx c' => c = c'
    | .emit e, .emit e' => e = e'
    | _, _ => False

theorem frameER_context {A : Type} (fr : ManagedHeap) (ctx : Ctx) :
    frameER (A := A) fr (CSLObs.ctx ctx) (CSLObs.ctx ctx) := rfl

theorem frameER_emit {A : Type} (fr : ManagedHeap) (emission : Indexed A) :
    frameER fr (CSLObs.emit emission) (CSLObs.emit emission) := rfl

theorem frameER_heap {A : Type} (fr : ManagedHeap) (s s' : SSig) (h : frame_rel fr s s') :
    frameER (A := A) fr (CSLObs.heap (csl_memory s)) (CSLObs.heap (csl_memory s')) :=
  ⟨h.1.1, h.1.2, h.2.2⟩

theorem frameER_right_unique {A : Type} (fr : ManagedHeap) :
    event_right_unique (frameER (A := A) fr) := by
  intro e e1 e2 h1 h2
  cases e <;> cases e1 <;> cases e2 <;> simp only [frameER] at h1 h2 <;>
    first | exact h1.elim | exact h2.elim | skip
  · exact congrArg CSLObs.heap
      (managed_heap_ext _ _ (peq_trans _ _ _ h1.2.2 (peq_sym _ _ h2.2.2)))
  · exact congrArg CSLObs.ctx (h1.symm.trans h2)
  · exact congrArg CSLObs.emit (h1.symm.trans h2)

/-- Preserve scheduling picks while transporting program observations. -/
def policyER {W : Type} (ER : event_rel (writerE W)) : event_rel (writerE (W ⊕ Nat)) :=
  fun (o o' : W ⊕ Nat) =>
    match o, o' with
    | .inl p, .inl p' => ER p p'
    | .inr i, .inr i' => i = i'
    | _, _ => False

theorem policyER_right_unique {W : Type} (ER : event_rel (writerE W)) :
    event_right_unique ER → event_right_unique (policyER ER) := by
  intro HU e e1 e2 h1 h2
  cases e <;> cases e1 <;> cases e2 <;> simp only [policyER] at h1 h2 <;>
    first | exact h1.elim | exact h2.elim | skip
  · exact congrArg Sum.inl (HU _ _ _ h1 h2)
  · exact congrArg Sum.inr (h1.symm.trans h2)

def frameERW {A : Type} (fr : ManagedHeap) : event_rel (writerE (CSLObs A ⊕ Nat)) :=
  policyER (frameER fr)

theorem frameERW_context {A : Type} (fr : ManagedHeap) (ctx : Ctx) :
    frameERW (A := A) fr (Sum.inl (CSLObs.ctx ctx)) (Sum.inl (CSLObs.ctx ctx)) := rfl

theorem frameERW_emit {A : Type} (fr : ManagedHeap) (emission : Indexed A) :
    frameERW fr (Sum.inl (CSLObs.emit emission)) (Sum.inl (CSLObs.emit emission)) := rfl

theorem frameERW_heap {A : Type} (fr : ManagedHeap) (s s' : SSig) (h : frame_rel fr s s') :
    frameERW (A := A) fr (Sum.inl (CSLObs.heap (csl_memory s)))
      (Sum.inl (CSLObs.heap (csl_memory s'))) :=
  frameER_heap (A := A) fr s s' h

theorem frameERW_pick {A : Type} (fr : ManagedHeap) (i : Nat) :
    frameERW (A := A) fr (Sum.inr i) (Sum.inr i) := rfl

theorem frameERW_right_unique {A : Type} (fr : ManagedHeap) :
    event_right_unique (frameERW (A := A) fr) :=
  policyER_right_unique _ (frameER_right_unique fr)

/-- Framing determines a unique target result, including both heap functions. -/
theorem frameRV_right_unique {X : Type} (fr : ManagedHeap) (r r1 r2 : X × SSig) :
    frameRV fr r r1 → frameRV fr r r2 → r1 = r2 := by
  obtain ⟨x1, m1, aux1⟩ := r1
  obtain ⟨x2, m2, aux2⟩ := r2
  rintro ⟨rfl, -, rfl, Hm1⟩ ⟨rfl, -, rfl, Hm2⟩
  cases managed_heap_ext _ _ (peq_trans _ _ _ Hm1 (peq_sym _ _ Hm2))
  rfl

/-- Frame both the returned state/value and the preceding observation. -/
def frame_post {A X : Type} (fr : ManagedHeap) (P : X × SSig → World (writerE (CSLObs A)) → Prop) :
    X × SSig → World (writerE (CSLObs A)) → Prop :=
  fun x' w' => ∃ x w, frameRV fr x x' ∧ simW (frameER fr) (frameRV (X := X) fr) w w' ∧ P x w

/-- Logged runners retain transport of the preceding world, including picks. -/
def frame_postW {A X : Type} (fr : ManagedHeap)
    (P : X × SSig → World (writerE (CSLObs A ⊕ Nat)) → Prop) :
    X × SSig → World (writerE (CSLObs A ⊕ Nat)) → Prop :=
  fun x' w' => ∃ x w, frameRV fr x x' ∧ simW (frameERW fr) (frameRV (X := X) fr) w w' ∧ P x w

/-- A disjoint well-formed source is related to its explicitly framed state. -/
theorem frame_rel_state (fr : ManagedHeap) (s : SSig) (h : frame_inv fr s) :
    frame_rel fr s (frame_state fr s) :=
  ⟨h, rfl, peq_refl _⟩

/-- State interpretation preserves finite guarded-step prefixes. -/
theorem guards_to_step_interp_state {E F B : Effect.{u}} {X S : Type u}
    (h : (e : E.I) → StateT S (CTree F B) (E.O e)) (t : CTree E B X) (s : S)
    (ht : guards_to_step t) : guards_to_step (interp_state h t s) := by
  induction ht with
  | step t u H =>
    exact .step _ (.guard (interp_state h u s)) (by rw [unfold_interp_state, H, unfold_step])
  | guard t u H _ ih =>
    exact .guard _ (interp_state h u s) (by rw [unfold_interp_state, H, unfold_guard]) ih

/-- Reading an owned cell agrees in frame-related states. -/
theorem frame_rel_read (fr : ManagedHeap) (s s' : SSig) (a v : Nat) (H : frame_rel fr s s')
    (HV : (csl_memory s).1 a = some v) : (csl_memory s').1 a = some v := by
  rw [H.2.2.1 a]; exact managed_read_pop _ fr a v H.1.1 HV

/-- Writing an owned cell preserves the frame relation. -/
theorem frame_rel_write (fr : ManagedHeap) (s s' : SSig) (a v : Nat) (H : frame_rel fr s s')
    (HV : (csl_memory s).1 a ≠ none) :
    frame_rel fr ((upd (csl_memory s).1 a v, (csl_memory s).2), s.2)
      ((upd (csl_memory s').1 a v, (csl_memory s').2), s'.2) := by
  obtain ⟨⟨h, al⟩, aux⟩ := s
  obtain ⟨⟨h', al'⟩, aux'⟩ := s'
  obtain ⟨⟨HD, HW⟩, HA, HE, HEa⟩ := H
  obtain ⟨HD', HE'⟩ := managed_write_pop (h, al) fr a v HD HV
  exact ⟨⟨HD', managed_write_preserves_wf _ _ _ _ HW⟩, HA,
    heq_trans _ _ _ (upd_heq _ _ _ _ HE) (heq_sym _ _ HE'.1), HEa⟩

/-- Auxiliary-state updates preserve the frame relation. -/
theorem frame_rel_aux (fr : ManagedHeap) (s s' : SSig) (a : Ctx × Nat) (H : frame_rel fr s s') :
    frame_rel fr (csl_memory s, a) (csl_memory s', a) :=
  ⟨H.1, rfl, H.2.2⟩

/-! ## Framing is a property of the handler

A response is stuck, a related return, or related observations followed by related returns.
Mutation snapshots change when a frame is added; contexts, indexed emissions and scheduling picks
retain their payload. -/

inductive frame_resp {Wo Y : Type} (ER : event_rel (writerE Wo)) (fr : ManagedHeap) :
    ctreeW Wo Bn (Y × SSig) → ctreeW Wo Bn (Y × SSig) → Prop
  | stuck (t t' : ctreeW Wo Bn (Y × SSig)) : t = .stuck → frame_resp ER fr t t'
  | ret (t t' : ctreeW Wo Bn (Y × SSig)) (s : SSig) (x : Y) (s' : SSig) : frame_rel fr s s' →
      t = pure (x, s) → t' = pure (x, s') → frame_resp ER fr t t'
  | log (t t' : ctreeW Wo Bn (Y × SSig)) (o o' : Wo) (s : SSig) (x : Y) (s' : SSig) : ER o o' →
      frame_rel fr s s' → t = .vis (E := writerE Wo) o (fun _ => pure (x, s)) →
      t' = .vis (E := writerE Wo) o' (fun _ => pure (x, s')) → frame_resp ER fr t t'

def FrameHandler {Es : Effect.{0}} {Wo : Type}
    (h : (e : Es.I) → StateT SSig (ctreeW Wo Bn) (Es.O e)) (okE : Es.I → Prop)
    (ER : ManagedHeap → event_rel (writerE Wo)) : Prop :=
  ∀ fr (e : Es.I) s s', okE e → frame_rel fr s s' → frame_resp (ER fr) fr (h e s) (h e s')

/-- Relabelling preserves response shape and lifts its observation relation. -/
theorem frame_resp_translate {W Y : Type} (ER : event_rel (writerE W)) (fr : ManagedHeap)
    (t t' : ctreeW W Bn (Y × SSig)) (H : frame_resp ER fr t t') :
    frame_resp (policyER ER) fr (translate relabel_log t) (translate relabel_log t') := by
  cases H with
  | stuck E => exact .stuck _ _ (by rw [E]; exact translate_stuck_node _)
  | ret s x s' HR E E' =>
    exact .ret _ _ s x s' HR (by rw [E, translate_ret]) (by rw [E', translate_ret])
  | log o o' s x s' HE HR E E' =>
    exact .log _ _ (.inl o) (.inl o') s x s' HE HR (by rw [E, translate_vis]; simp [relabel_log])
      (by rw [E', translate_vis]; simp [relabel_log])

/-- A policy adds only equal scheduling observations and preserves state. -/
theorem policy_handler_frame {E : Effect.{0}} {W : Type}
    (h : (e : E.I) → StateT SSig (ctreeW W Bn) (E.O e)) (okE : E.I → Prop)
    (ER : ManagedHeap → event_rel (writerE W)) (HH : FrameHandler h okE ER) :
    FrameHandler (policy_handler h) (okE_policy okE) (fun fr => policyER (ER fr)) := by
  rintro fr (e | i) s s' Hok HR
  · exact frame_resp_translate _ fr _ _ (HH fr e s s' Hok HR)
  · exact .log _ _ (.inr i) (.inr i) s ⟨⟩ s' rfl HR rfl rfl

section FrameCore
variable {Es : Effect.{0}} {Wo : Type} (h : (e : Es.I) → StateT SSig (ctreeW Wo Bn) (Es.O e))
  (okE : Es.I → Prop) (ER : ManagedHeap → event_rel (writerE Wo)) (HH : FrameHandler h okE ER)

/-- Structural invariant: both trees interpret the same source under frame-related states. -/
def frame_tree {X : Type} (fr : ManagedHeap) (t t' : ctreeW Wo Bn (X × SSig)) : Prop :=
  ∃ (u : CTree Es Bn X) (s s' : SSig), Framable okE u ∧ frame_rel fr s s' ∧
    t = interp_state h u s ∧ t' = interp_state h u s'

/-- The same framable source in related states establishes the invariant. -/
theorem frame_tree_intro {X : Type} (fr : ManagedHeap) (u : CTree Es Bn X) (s s' : SSig)
    (HF : Framable okE u) (HR : frame_rel fr s s') :
    frame_tree h okE fr (interp_state h u s) (interp_state h u s') :=
  ⟨u, s, s', HF, HR, rfl, rfl⟩

/-- Leading guards preserve the interpreter invariant. -/
theorem frame_tree_guard {X : Type} (fr : ManagedHeap) (u : CTree Es Bn X) (s s' : SSig)
    (HF : Framable okE u) (HR : frame_rel fr s s') :
    frame_tree h okE fr (.guard (interp_state h u s)) (.guard (interp_state h u s')) := by
  rw [← interp_state_guard, ← interp_state_guard]
  exact frame_tree_intro h okE fr _ s s' (fr_guard okE u HF) HR

include HH in
/-- One interpreter step preserves `frame_tree`, by cases on the framable source node. -/
theorem frame_shape {X : Type} (fr : ManagedHeap) (u : CTree Es Bn X) (s s' : SSig)
    (HF : Framable okE u) (HR : frame_rel fr s s') :
    csim_shape (ER fr) (frameRV fr) (frame_tree h okE fr)
      (interp_state h u s).unfold (interp_state h u s').unfold := by
  have HF := (framable_unfold okE u).1 HF
  rw [unfold_interp_state, unfold_interp_state]
  generalize u.unfold = ou at HF ⊢
  cases HF with
  | ret x => rw [unfold_pure, unfold_pure]; exact .ret _ _ ⟨rfl, HR⟩
  | stuck => rw [unfold_stuck]; exact .stuck _
  | step t ht =>
    rw [unfold_step, unfold_step]; exact .step _ _ (frame_tree_guard h okE fr t s s' ht HR)
  | guard t ht =>
    rw [unfold_guard, unfold_guard]; exact .guard _ _ (frame_tree_intro h okE fr t s s' ht HR)
  | vis e k he hk =>
    dsimp only
    cases HH fr e s s' he HR with
    | stuck Er => rw [Er, stuck_bind, unfold_stuck]; exact .stuck _
    | ret s0 x s0' HR0 Er Er' =>
      rw [Er, Er', pure_bind', pure_bind', unfold_guard, unfold_guard]
      exact .guard _ _ (frame_tree_intro h okE fr _ s0 s0' (hk x) HR0)
    | log o o' s0 x s0' HE HR0 Er Er' =>
      rw [Er, Er', vis_bind, vis_bind, unfold_vis, unfold_vis]
      refine .vis _ _ _ _ HE rfl fun _ _ _ => ?_
      simp only [pure_bind']
      exact frame_tree_guard h okE fr _ s0 s0' (hk x) HR0
  | br c k hg hk =>
    dsimp only
    simp only [mbr, CTree.branch', CTree.br', br_bind, pure_bind', unfold_br]
    exact .br _ _ _ (fun y => guards_to_step_can_trans _ (guards_to_step_guard _
      (guards_to_step_interp_state h _ s (hg y))))
      fun y => frame_tree_guard h okE fr _ s s' (hk y) HR

include HH in
/-- Interpreting a framable source in related states gives a conditional simulation. -/
theorem csim_interp_frame {X : Type} (fr : ManagedHeap) (u : CTree Es Bn X) (s s' : SSig)
    (HF : Framable okE u) (HR : frame_rel fr s s') :
    csim (ER fr) (frameRV fr) (interp_state h u s) (interp_state h u s') :=
  csim_structural (ER fr) (frameRV fr) (frame_tree h okE fr)
    (fun _ _ ⟨v, σ, σ', HV, Hσ, HE, HE'⟩ => by
      subst HE HE'; exact frame_shape h okE ER HH fr v σ σ' HV Hσ)
    _ _ (frame_tree_intro h okE fr u s s' HF HR)

/-- Uniqueness side condition of `ticl_csim` for the frame relations. -/
private theorem frame_sim_unique {X : Type} (b : Bool) (fr : ManagedHeap)
    (HU : event_right_unique (ER fr)) : sim_unique b (ER fr) (frameRV (X := X) fr) := by
  cases b
  · trivial
  · exact ⟨HU, frameRV_right_unique fr⟩

include HH in
theorem ticl_interp_frame {X : Type} {b : Bool} (fr : ManagedHeap) (u : CTree Es Bn X)
    (s s' : SSig) (p : TiclAt (writerE Wo) (X × SSig) b) (w w' : World (writerE Wo))
    (HU : event_right_unique (ER fr)) (HF : Framable okE u) (HR : frame_rel fr s s')
    (HW : simW (ER fr) (frameRV (X := X) fr) w w') (HP : entails p (interp_state h u s) w) :
    entails (framer (X × SSig) b (ER fr) (frameRV fr) p) (interp_state h u s') w' :=
  ticl_csim b (ER fr) (frameRV fr) p (frame_sim_unique ER b fr HU) _ _ w w'
    (csim_interp_frame h okE ER HH fr u s s' HF HR) HW HP

include HH in
/-- Related leading logs retain every atom, including nested formulas. -/
theorem ticl_interp_frame_log {X : Type} {b : Bool} (fr : ManagedHeap) (u : CTree Es Bn X)
    (s s' : SSig) (o o' : Wo) (p : TiclAt (writerE Wo) (X × SSig) b) (w w' : World (writerE Wo))
    (HU : event_right_unique (ER fr)) (HF : Framable okE u) (HR : frame_rel fr s s')
    (HE : ER fr o o') (HW : simW (ER fr) (frameRV (X := X) fr) w w')
    (HP : entails p (log o >>= fun _ => interp_state h u s) w) :
    entails (framer (X × SSig) b (ER fr) (frameRV fr) p)
      (log o' >>= fun _ => interp_state h u s') w' := by
  have HC := csim_interp_frame h okE ER HH fr u s s' HF HR
  refine ticl_csim b (ER fr) (frameRV fr) p (frame_sim_unique ER b fr HU) _ _ w w' ?_ HW HP
  simp only [log, vis_bind, pure_bind']
  refine b_chain (gfp_chain (csimF (ER fr) (frameRV fr))) _ _
    ⟨fun l t1 ht => ?_, fun _ l' t1' ht' => ?_⟩
  · obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
    exact ⟨_, _, trans_vis PUnit.unit _, .obs _ _ _ _ HE HEq.rfl, HC⟩
  · obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht'
    exact ⟨_, _, trans_vis PUnit.unit _, .obs _ _ _ _ HE HEq.rfl, HC⟩

end FrameCore

/-! ## The CSL handler frames -/

/-- Checked heap responses frame, including whole-block free and snapshots. -/
theorem sh_frame_handler : FrameHandler (sh (A := Nat × Nat)) no_alloc_sE frameER := by
  intro fr e s s' Hok HR
  obtain ⟨⟨h, al⟩, aux⟩ := s
  obtain ⟨⟨h', al'⟩, aux'⟩ := s'
  obtain rfl : aux = aux' := HR.2.1.symm
  rcases e with e | e | e
  · cases e with
    | read a =>
      show frame_resp _ _ (heap_handlerW CSLObs.heap (.read a) ((h, al), aux))
        (heap_handlerW CSLObs.heap (.read a) ((h', al'), aux))
      cases HV : h a with
      | some current =>
        have HV' := frame_rel_read fr ((h, al), aux) ((h', al'), aux) a current HR HV
        rw [heap_handlerW_rd_some _ a h al aux current HV,
          heap_handlerW_rd_some _ a h' al' aux current HV']
        exact .ret _ _ _ _ _ HR rfl rfl
      | none => exact .stuck _ _ (heap_handlerW_rd_none _ a h al aux HV)
    | write a v =>
      show frame_resp _ _ (heap_handlerW CSLObs.heap (.write a v) ((h, al), aux))
        (heap_handlerW CSLObs.heap (.write a v) ((h', al'), aux))
      cases HV : h a with
      | some current =>
        have HV' := frame_rel_read fr ((h, al), aux) ((h', al'), aux) a current HR HV
        have HRw := frame_rel_write fr ((h, al), aux) ((h', al'), aux) a v HR
          (by simp [csl_memory, HV])
        rw [heap_handlerW_wr_some _ a h al aux v current HV,
          heap_handlerW_wr_some _ a h' al' aux v current HV', log_vis, log_vis]
        exact .log _ _ _ _ _ _ _ (frameER_heap fr _ _ HRw) HRw rfl rfl
      | none => exact .stuck _ _ (heap_handlerW_wr_none _ a h al aux v HV)
    | alloc n => exact Hok.elim
    | free a =>
      show frame_resp _ _ (heap_handlerW CSLObs.heap (.free a) ((h, al), aux))
        (heap_handlerW CSLObs.heap (.free a) ((h', al'), aux))
      cases HM : managed_free (h, al) a with
      | none => exact .stuck _ _ (heap_handlerW_free_invalid _ a _ aux HM)
      | some memory =>
        obtain ⟨⟨HD, HW⟩, -, HE⟩ := HR
        obtain ⟨⟨mf, HF, HEf⟩, HDf⟩ := managed_free_pop _ _ _ _ HD HW HM
        obtain ⟨mb, HB, HEb⟩ := managed_free_peq _ _ _ _ (peq_sym _ _ HE) HF
        have HRf : frame_rel fr (memory, aux) (mb, aux) :=
          ⟨⟨HDf, managed_free_preserves_wf _ _ _ HW HM⟩, rfl,
            peq_trans _ _ _ (peq_sym _ _ HEb) HEf⟩
        rw [heap_handlerW_free _ a _ memory aux HM, heap_handlerW_free _ a (h', al') mb aux HB]
        cases a with
        | zero => exact .ret _ _ _ _ _ HRf rfl rfl
        | succ n =>
          simp only [log_vis]
          exact .log _ _ _ _ _ _ _ (frameER_heap fr _ _ HRf) HRf rfl rfl
    | cas a expected desired =>
      show frame_resp _ _ (heap_handlerW CSLObs.heap (.cas a expected desired) ((h, al), aux))
        (heap_handlerW CSLObs.heap (.cas a expected desired) ((h', al'), aux))
      cases HV : h a with
      | some current =>
        have HV' := frame_rel_read fr ((h, al), aux) ((h', al'), aux) a current HR HV
        by_cases HC : current = expected
        · subst HC
          have HRw := frame_rel_write fr ((h, al), aux) ((h', al'), aux) a desired HR
            (by simp [csl_memory, HV])
          rw [heap_handlerW_cas_success _ a current desired h al aux HV,
            heap_handlerW_cas_success _ a current desired h' al' aux HV', log_vis, log_vis]
          exact .log _ _ _ _ _ _ _ (frameER_heap fr _ _ HRw) HRw rfl rfl
        · rw [heap_handlerW_cas_failure _ a expected desired current h al aux HV HC,
            heap_handlerW_cas_failure _ a expected desired current h' al' aux HV' HC]
          exact .ret _ _ _ _ _ HR rfl rfl
      | none => exact .stuck _ _ (heap_handlerW_cas_missing _ a expected desired h al aux HV)
  · cases e with
    | get => exact .ret _ _ _ _ _ HR rfl rfl
    | put ctx =>
      have HRctx := frame_rel_aux fr ((h, al), aux) ((h', al'), aux) (ctx, aux.2) HR
      exact .log _ _ _ _ _ _ _ (frameER_context fr ctx) HRctx (log_vis _ _) (log_vis _ _)
  · have HRemit := frame_rel_aux fr ((h, al), aux) ((h', al'), aux) (aux.1, aux.2 + 1) HR
    exact .log _ _ _ _ _ _ _ (frameER_emit fr (stamp e aux.2)) HRemit (log_vis _ _)
      (log_vis _ _)

theorem csim_interp_sh_frame {X : Type} (fr : ManagedHeap) (u : CTree sE Bn X) (s s' : SSig)
    (HF : Framable no_alloc_sE u) (HR : frame_rel fr s s') :
    csim (frameER fr) (frameRV fr) (interp_state sh u s) (interp_state sh u s') :=
  csim_interp_frame sh no_alloc_sE frameER sh_frame_handler fr u s s' HF HR

theorem ticl_csl_frame_log {X : Type} {b : Bool} (fr : ManagedHeap) (u : CTree sE Bn X)
    (s s' : SSig) (o o' : CSLObs (Nat × Nat))
    (p : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b) (w w' : World _)
    (HF : Framable no_alloc_sE u) (HR : frame_rel fr s s') (HE : frameER fr o o')
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (HP : entails p (log o >>= fun _ => interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) p)
      (log o' >>= fun _ => interp_state sh u s') w' :=
  ticl_interp_frame_log sh no_alloc_sE frameER sh_frame_handler fr u s s' o o' p w w'
    (frameER_right_unique fr) HF HR HE HW HP

/-- Any instrumented policy, including ordinary RR, shares this handler. -/
theorem ticl_csl_frameW {X : Type} {b : Bool} (fr : ManagedHeap) (u : CTree (sE ⊕ₑ schedE) Bn X)
    (s s' : SSig) (HF : Framable (okE_policy no_alloc_sE) u) (HR : frame_rel fr s s')
    (p : TiclAt (writerE (CSLObs (Nat × Nat) ⊕ Nat)) (X × SSig) b) (w w' : World _)
    (HW : simW (frameERW fr) (frameRV (X := X) fr) w w')
    (HP : entails p (interp_state (policy_handler sh) u s) w) :
    entails (framer (X × SSig) b (frameERW fr) (frameRV fr) p)
      (interp_state (policy_handler sh) u s') w' :=
  ticl_interp_frame (policy_handler sh) (okE_policy no_alloc_sE) frameERW
    (policy_handler_frame sh no_alloc_sE frameER sh_frame_handler)
    fr u s s' p w w' (frameERW_right_unique fr) HF HR HW HP

theorem ticl_csl_frameW_log {X : Type} {b : Bool} (fr : ManagedHeap)
    (u : CTree (sE ⊕ₑ schedE) Bn X) (s s' : SSig) (o o' : CSLObs (Nat × Nat) ⊕ Nat)
    (p : TiclAt (writerE (CSLObs (Nat × Nat) ⊕ Nat)) (X × SSig) b) (w w' : World _)
    (HF : Framable (okE_policy no_alloc_sE) u) (HR : frame_rel fr s s') (HE : frameERW fr o o')
    (HW : simW (frameERW fr) (frameRV (X := X) fr) w w')
    (HP : entails p (log o >>= fun _ => interp_state (policy_handler sh) u s) w) :
    entails (framer (X × SSig) b (frameERW fr) (frameRV fr) p)
      (log o' >>= fun _ => interp_state (policy_handler sh) u s') w' :=
  ticl_interp_frame_log (policy_handler sh) (okE_policy no_alloc_sE) frameERW
    (policy_handler_frame sh no_alloc_sE frameER sh_frame_handler)
    fr u s s' o o' p w w' (frameERW_right_unique fr) HF HR HE HW HP

theorem ticl_csl_frameW_stable {X : Type} (fr : ManagedHeap) (u : CTree (sE ⊕ₑ schedE) Bn X)
    (s s' : SSig) (HF : Framable (okE_policy no_alloc_sE) u) (HR : frame_rel fr s s')
    (p : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat))) (w w' : World _)
    (HS : prefix_stable (frameERW fr) (frameRV (X := X) fr) p)
    (HW : simW (frameERW fr) (frameRV (X := X) fr) w w')
    (H : entails p (interp_state (policy_handler sh) u s) w) :
    entails p (interp_state (policy_handler sh) u s') w' :=
  prefix_stable_framer (M := CTree) (B := Bn) _ _ _ p HS _ _
    (ticl_csl_frameW (b := false) fr u s s' HF HR p w w' HW H)

/-! ## Formula and postcondition framing

All-formula transport requires related histories; stable prefixes may retain their original
syntax. -/

section FrameLogic
variable {X : Type} (fr : ManagedHeap) (u : CTree sE Bn X) (s s' : SSig)
  (HF : Framable no_alloc_sE u) (HR : frame_rel fr s s')
include HF HR

theorem ticl_csl_frame {b : Bool} (p : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b)
    (w w' : World _) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails p (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) p) (interp_state sh u s') w' :=
  ticl_csim b (frameER fr) (frameRV fr) p (frame_sim_unique (fun fr => frameER fr) b fr
    (frameER_right_unique fr)) _ _ w w' (csim_interp_sh_frame fr u s s' HF HR) HW H

theorem an_csl_frame {b : Bool} (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b) (w w' : World _)
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cx .A phi psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (.cx .A phi psi))
      (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem en_csl_frame {b : Bool} (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b) (w w' : World _)
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cx .E phi psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (.cx .E phi psi))
      (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem au_csl_frame {b : Bool} (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b) (w w' : World _)
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cu .A phi psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (.cu .A phi psi))
      (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem eu_csl_frame {b : Bool} (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b) (w w' : World _)
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cu .E phi psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (.cu .E phi psi))
      (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem ag_csl_frame (phi : TiclL (writerE (CSLObs (Nat × Nat)))) (w w' : World _)
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (Ticl.cg .A phi) (interp_state sh u s) w) :
    entails (framer (X × SSig) false (frameER fr) (frameRV fr) (Ticl.cg .A phi))
      (interp_state sh u s') w' :=
  ticl_csl_frame (b := false) fr u s s' HF HR _ w w' HW H

theorem eg_csl_frame (phi : TiclL (writerE (CSLObs (Nat × Nat)))) (w w' : World _)
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (Ticl.cg .E phi) (interp_state sh u s) w) :
    entails (framer (X × SSig) false (frameER fr) (frameRV fr) (Ticl.cg .E phi))
      (interp_state sh u s') w' :=
  ticl_csl_frame (b := false) fr u s s' HF HR _ w w' HW H

theorem ax_csl_frame {b : Bool} (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b)
    (w w' : World _) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (AX psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (AX psi)) (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem ex_csl_frame {b : Bool} (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b)
    (w w' : World _) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (EX psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (EX psi)) (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem af_csl_frame {b : Bool} (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b)
    (w w' : World _) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (AF psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (AF psi)) (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem ef_csl_frame {b : Bool} (psi : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b)
    (w w' : World _) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (EF psi) (interp_state sh u s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) (EF psi)) (interp_state sh u s') w' :=
  ticl_csl_frame fr u s s' HF HR _ w w' HW H

theorem ticl_csl_frame_stable (p : TiclL (writerE (CSLObs (Nat × Nat)))) (w w' : World _)
    (HS : prefix_stable (frameER fr) (frameRV (X := X) fr) p)
    (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails p (interp_state sh u s) w) : entails p (interp_state sh u s') w' :=
  prefix_stable_framer (M := CTree) (B := Bn) _ _ _ p HS _ _
    (ticl_csl_frame (b := false) fr u s s' HF HR p w w' HW H)

theorem anr_csl_frame_ret (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cx .A phi (.ret P)) (interp_state sh u s) w) :
    entails (.cx .A (framer (X × SSig) false (frameER fr) (frameRV fr) phi)
      (.ret (frame_post fr P))) (interp_state sh u s') w' :=
  ticl_csl_frame (b := true) fr u s s' HF HR (.cx .A phi (.ret P)) w w' HW H

theorem aur_csl_frame_ret (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cu .A phi (.ret P)) (interp_state sh u s) w) :
    entails (.cu .A (framer (X × SSig) false (frameER fr) (frameRV fr) phi)
      (.ret (frame_post fr P))) (interp_state sh u s') w' :=
  ticl_csl_frame (b := true) fr u s s' HF HR (.cu .A phi (.ret P)) w w' HW H

theorem enr_csl_frame_ret (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cx .E phi (.ret P)) (interp_state sh u s) w) :
    entails (.cx .E (framer (X × SSig) false (frameER fr) (frameRV fr) phi)
      (.ret (frame_post fr P))) (interp_state sh u s') w' :=
  ticl_csl_frame (b := true) fr u s s' HF HR (.cx .E phi (.ret P)) w w' HW H

theorem eur_csl_frame_ret (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails (.cu .E phi (.ret P)) (interp_state sh u s) w) :
    entails (.cu .E (framer (X × SSig) false (frameER fr) (frameRV fr) phi)
      (.ret (frame_post fr P))) (interp_state sh u s') w' :=
  ticl_csl_frame (b := true) fr u s s' HF HR (.cu .E phi (.ret P)) w w' HW H

omit HF HR in
/-- Prefix transport for the `_done` corollaries. -/
private theorem frame_prefix (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (t t' : CTree (writerE (CSLObs (Nat × Nat))) Bn (X × SSig)) (z z' : World _)
    (hS : csim (frameER fr) (frameRV fr) t t')
    (hZ : simW (frameER fr) (frameRV (X := X) fr) z z')
    (hP : entails phi t z) :
    entails (framer (X × SSig) false (frameER fr) (frameRV fr) phi) t' z' :=
  ticl_csim false (frameER fr) (frameRV fr) phi trivial t t' z z' hS hZ hP

theorem anr_csl_frame_done (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : anc (entails phi) (fun _ wd => DoneWith P wd) (interp_state sh u s) w) :
    anc (entails (framer (X × SSig) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => DoneWith (frame_post fr P) wd) (interp_state sh u s') w' :=
  sim_anc ctree_kripke ctree_kripke (frameER fr) (frameRV fr) (csim (frameER fr) (frameRV fr))
    (csim_ktrans_l _ _) (csim_ktrans_r _ _) _ _ _ _ (frame_prefix fr phi)
    (fun _ _ z z' _ hZ hP => sim_done_with (frameER fr) (frameRV fr) P z z' hZ hP)
    _ _ w w' (csim_interp_sh_frame fr u s s' HF HR) HW H

theorem aur_csl_frame_done (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : Auc (entails phi) (fun _ wd => DoneWith P wd) (interp_state sh u s) w) :
    Auc (entails (framer (X × SSig) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => DoneWith (frame_post fr P) wd) (interp_state sh u s') w' :=
  sim_auc ctree_kripke ctree_kripke (frameER fr) (frameRV fr) (csim (frameER fr) (frameRV fr))
    (csim_ktrans_l _ _) (csim_ktrans_r _ _) _ _ _ _ (frame_prefix fr phi)
    (fun _ _ z z' _ hZ hP => sim_done_with (frameER fr) (frameRV fr) P z z' hZ hP)
    _ _ w w' (csim_interp_sh_frame fr u s s' HF HR) HW H

theorem enr_csl_frame_done (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : enc (entails phi) (fun _ wd => DoneWith P wd) (interp_state sh u s) w) :
    enc (entails (framer (X × SSig) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => DoneWith (frame_post fr P) wd) (interp_state sh u s') w' :=
  sim_enc ctree_kripke ctree_kripke (frameER fr) (frameRV fr) (csim (frameER fr) (frameRV fr))
    (csim_ktrans_l _ _) _ _ _ _ (frame_prefix fr phi)
    (fun _ _ z z' _ hZ hP => sim_done_with (frameER fr) (frameRV fr) P z z' hZ hP)
    _ _ w w' (csim_interp_sh_frame fr u s s' HF HR) HW H

theorem eur_csl_frame_done (phi : TiclL (writerE (CSLObs (Nat × Nat))))
    (P : X × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop) (w w' : World _)
    (_ : NotDone w) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : Euc (entails phi) (fun _ wd => DoneWith P wd) (interp_state sh u s) w) :
    Euc (entails (framer (X × SSig) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => DoneWith (frame_post fr P) wd) (interp_state sh u s') w' :=
  sim_euc ctree_kripke ctree_kripke (frameER fr) (frameRV fr) (csim (frameER fr) (frameRV fr))
    (csim_ktrans_l _ _) _ _ _ _ (frame_prefix fr phi)
    (fun _ _ z z' _ hZ hP => sim_done_with (frameER fr) (frameRV fr) P z z' hZ hP)
    _ _ w w' (csim_interp_sh_frame fr u s s' HF HR) HW H

end FrameLogic

/-- A single absolute allocation frames only when both heaps have the same first-fit witness and
their complete managed post-states remain related. -/
theorem ticl_csl_alloc_frame_at {X : Type} {b : Bool} (fr : ManagedHeap) (size base : Nat)
    (K : Nat → CTree sE Bn X) (s s' : SSig)
    (p : TiclAt (writerE (CSLObs (Nat × Nat))) (X × SSig) b) (w w' : World _)
    (HR : frame_rel fr s s') (Pos : 0 < size) (Base : 0 < base)
    (Free : block_free (csl_memory s).1 base size) (Free' : block_free (csl_memory s').1 base size)
    (First : ∀ j, 0 < j → j < base → ¬ block_free (csl_memory s).1 j size)
    (First' : ∀ j, 0 < j → j < base → ¬ block_free (csl_memory s').1 j size)
    (HRpost : frame_rel fr (managed_alloc (csl_memory s) base size, s.2)
      (managed_alloc (csl_memory s') base size, s'.2))
    (HF : Framable no_alloc_sE (K base)) (HW : simW (frameER fr) (frameRV (X := X) fr) w w')
    (H : entails p (interp_state sh (heap_alloc size >>= K) s) w) :
    entails (framer (X × SSig) b (frameER fr) (frameRV fr) p)
      (interp_state sh (heap_alloc size >>= K) s') w' := by
  obtain ⟨⟨h, allocs⟩, aux⟩ := s
  obtain ⟨⟨h', allocs'⟩, aux'⟩ := s'
  have Ealloc := interp_heapW_alloc_first CSLObs.heap
    (h_sum csl_context_handler (csl_emit_handler (A := Nat × Nat)))
    h allocs size base aux K Pos Base Free First
  have Ealloc' := interp_heapW_alloc_first CSLObs.heap
    (h_sum csl_context_handler (csl_emit_handler (A := Nat × Nat)))
    h' allocs' size base aux' K Pos Base Free' First'
  have H := (proper_entails_meq p Ealloc).1 H
  refine (proper_entails_meq _ Ealloc').2 ?_
  exact ticl_csl_frame_log fr (K base) _ _ _ _ p w w' HF HRpost (frameER_heap fr _ _ HRpost) HW H

-- Not ported: `frame_resp_equ`, `frame_tree_equ` (`Proper` instances for `equ`, which is `=`);
-- the `response_log` Ltac (replaced by the equation `Tisl.log_vis`).

end Tisl.CSL
