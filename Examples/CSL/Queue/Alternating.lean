/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Operations

/-!
# Two queues under a nonpreemptive alternating scheduler

A turn is one complete rotation of the queue at `hdr`, its emissions tagged `q`. The cyclic
scheduler alternates between two queues by parity of the turn counter and logs one scheduling
decision after each completed turn (← `examples/CSL/Queue/Alternating.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Alternating
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Examples.CSL.Queue.Representation
  Examples.CSL.Queue.Operations
open ITree (Effect)

/-! ## A turn -/

/-- One rotation of the queue at `hdr` tagged `q`, continuing as `kt`. -/
def turnk {X : Type} (q hdr : Nat) (kt : CTree sE Bn X) : CTree sE Bn X :=
  queue_turn (semit q) hdr kt

def turn (q hdr : Nat) : CTree sE Bn PUnit := turnk q hdr (pure ⟨⟩)

/-- `queue_turn_spec` with tagged observations, for an arbitrary tail. -/
theorem turnk_spec {X : Type} (q hdr a : Nat) (ns : List Nat) (pv : Nat) (vs : List Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (kt : CTree sE Bn X) :
    qrep hdr (a :: ns) (pv :: vs) h →
    interp_state sh (turnk q hdr kt) ((h, allocs), (ctx, c)) ~
      emit_list (queue_turn_logs (.emit (stamp (q, pv) c)) hdr a (ns.headD 0)
          ((a :: ns).getLastD 0) (h, allocs))
        (interp_state sh kt ((rot_heap hdr a (ns.headD 0) (zof hdr ns) h, allocs), (ctx, c + 1))) :=
  queue_turn_spec (semit q) (fun value index => .emit (stamp (q, value) index))
    (fun _ _ _ _ _ _ => interp_csl_emit _ _ _ _ _) hdr a ns pv vs h allocs ctx c kt

/-! ## The nonpreemptive cyclic scheduler

`n` is the turn counter; each completed turn ends with one logged scheduling decision. -/

/-- Rocq `if Nat.even n then u else v`. -/
def hdrof (u v n : Nat) : Nat := if n % 2 = 0 then u else v

def tagof (n : Nat) : Nat := if n % 2 = 0 then 1 else 2

/-- Queue 2 occupies slot `0`, queue 1 slot `1`. -/
def queue_slot (n : Nat) : Fin 2 := if n % 2 = 0 then 1 else 0

/-- One turn of the queue whose turn it is, then the scheduling decision for the next turn. -/
def sbody (u v n : Nat) : CTree (sE ⊕ₑ schedE) Bn (Nat ⊕ PUnit) :=
  translate (fun e => (⟨.inl e, id⟩ : (f : (sE ⊕ₑ schedE).I) × ((sE ⊕ₑ schedE).O f → sE.O e)))
    (turn (tagof n) (hdrof u v n)) >>= fun _ =>
  CTree.trigger (E := sE ⊕ₑ schedE) (.inr (slot_index (queue_slot (n + 1)))) >>= fun _ =>
  pure (.inl (n + 1))

def sched (u v n : Nat) : CTree (sE ⊕ₑ schedE) Bn PUnit := CTree.iter (sbody u v) n

def srun (u v n : Nat) (s : SSig) : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig) :=
  interp_state (policy_handler sh) (sched u v n) s

/-- One scheduler turn, for either phase. -/
theorem sbody_spec (u v n a : Nat) (ns : List Nat) (pv : Nat) (vs : List Nat) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    qrep (hdrof u v n) (a :: ns) (pv :: vs) h →
    interp_state (policy_handler sh) (sbody u v n) ((h, allocs), (ctx, c)) ~
      (emit_list ((queue_turn_logs (.emit (stamp (tagof n, pv) c)) (hdrof u v n) a (ns.headD 0)
            ((a :: ns).getLastD 0) (h, allocs)).map .inl)
        (log (.inr (slot_index (queue_slot (n + 1)))) >>= fun _ =>
          pure ((.inl (n + 1) : Nat ⊕ PUnit),
            ((rot_heap (hdrof u v n) a (ns.headD 0) (zof (hdrof u v n) ns) h, allocs),
              (ctx, c + 1))))
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn ((Nat ⊕ PUnit) × SSig)) := by
  intro Hq
  rw [sbody, interp_state_bind, interp_state_policy_translate, turn]
  refine sbisim_trans (sbisim_clo_bind_eq (translate_sbisim _
    (turnk_spec (tagof n) (hdrof u v n) a ns pv vs h allocs ctx c
      (pure PUnit.unit : CTree sE Bn PUnit) Hq)) fun _ => sbisim_refl _) ?_
  rw [translate_emit_list, emit_list_bind]
  refine emit_list_sbisim _ ?_
  rw [interp_state_ret, translate_ret, pure_bind', interp_state_bind]
  refine sbisim_trans (interp_state_trigger_bind _ _ _ _) ?_
  simp only [policy_handler, sched_handler, vis_bind, pure_bind', interp_state_ret, log]
  exact sbisim_refl _

/-- The parity flip: one turn changes whose turn it is (Rocq
`Nat.even (S n) = negb (Nat.even n)`). -/
theorem even_flip (n : Nat) : ((n + 1) % 2 = 0) ↔ ¬ (n % 2 = 0) := by omega

theorem hdrof_even (u v n : Nat) : n % 2 = 0 → hdrof u v n = u := fun h => by simp [hdrof, h]

theorem hdrof_odd (u v n : Nat) : n % 2 = 1 → hdrof u v n = v := fun h => by simp [hdrof, h]

theorem tagof_even (n : Nat) : n % 2 = 0 → tagof n = 1 := fun h => by simp [tagof, h]

theorem tagof_odd (n : Nat) : n % 2 = 1 → tagof n = 2 := fun h => by simp [tagof, h]

/-! ## Observation predicates

Tagged observations are `.emit` of `Indexed (Nat × Nat)`: the payload pairs the queue tag with
the value; a retained observation cannot masquerade as a later one
(`Tisl.indexed_excludes_retained`). -/

theorem turnk_bind {X : Type} (q hdr : Nat) (kt : CTree sE Bn X) :
    turnk q hdr kt = (turn q hdr >>= fun _ => kt) := by
  rw [turn, turnk, turnk, queue_turn_bind, pure_bind']

theorem srun_turn (u v n : Nat) (s : SSig) :
    srun u v n s ~
      (translate relabel_log (interp_state sh (turn (tagof n) (hdrof u v n)) s) >>= fun p =>
        .vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr (slot_index (queue_slot (n + 1))))
          fun _ => srun u v (n + 1) p.2) := by
  rw [srun, sched, interp_state_unfold_iter, sbody, interp_state_bind,
    interp_state_policy_translate, bind_assoc]
  refine sbisim_bind_eq _ fun p => ?_
  rw [interp_state_bind, bind_assoc]
  refine sbisim_trans (interp_state_trigger_bind _ _ _ _) ?_
  simp only [policy_handler, sched_handler, vis_bind, pure_bind', interp_state_ret]
  exact sb_vis _ fun _ => sb_guard _

end Examples.CSL.Queue.Alternating
