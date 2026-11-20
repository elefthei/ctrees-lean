/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Early

/-!
# CoCSL temporal rules under a scheduling policy

The round-robin half of the CoCSL modality matrix as one policy-generic kernel:
`x/u/ag/eg_csl_fair_*` rewrite `qnext`/`quntil`/`AG`/`EG` across one focused source instruction
under `interp_schedule_fair sch sh` for any `sch : Scheduler`. The scheduling points (`yield`, a
read variable) mention `rr_pick` and are stated for round robin directly; the remaining round-robin
names are `rr_scheduler` instances, kept only where used downstream (← `Lang/CoCSL/Mod.v`,
7673-11739).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx Tisl.Notation
open ITree (Effect)

local notation "WR" => writerE (CSLObs (Nat × Nat) ⊕ Nat)
local notation "TW" => ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)
local notation "RR" => interp_schedule_rr sh

section Helpers
variable {q : Ticlq} {P Q : TW → World WR → Prop} {t u : TW} {w : World WR}

private theorem sb_eq (e : t = u) : t ~ u := e ▸ sbisim_refl _

private theorem ag_spin {φ : TiclL WR} : ¬ entails (AG φ) (CTree.spin : TW) w :=
  fun h => let ⟨_, ⟨_, _, tr⟩, _⟩ := agc_unfold.1 h; spin_no_ktrans _ _ tr

private theorem eg_spin {φ : TiclL WR} : ¬ entails (EG φ) (CTree.spin : TW) w :=
  fun h => let ⟨_, _, _, tr, _⟩ := egc_unfold.1 h; spin_no_ktrans _ _ tr

end Helpers

/-! ## The policy-generic kernel -/

section FairKernel
variable (sch : Scheduler)

set_option hygiene false in
local notation "FAIR" => interp_schedule_fair sch sh

theorem x_csl_fair_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some value → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some
      i) st ((h, allocs), (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (K (some value)))
      (some i) st ((h, allocs), (ctx, c))) w) :=
  fun H0 => qnext_sb hP hQ ((interp_fair_read_value sch n ts i a value K st h allocs ctx c H0))

theorem u_csl_fair_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some value → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (K (some
      value))) (some i) st ((h, allocs), (ctx, c))) w) :=
  fun H0 => quntil_sb hP hQ ((interp_fair_read_value sch n ts i a value K st h allocs ctx c H0))

theorem ag_csl_fair_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    h a = some value → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (K (some
      value))) (some i) st ((h, allocs), (ctx, c))) w) :=
  fun H0 => proper_entails_meq _ ((interp_fair_read_value sch n ts i a value K st h allocs ctx c
    H0))

theorem eg_csl_fair_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    h a = some value → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (K (some
      value))) (some i) st ((h, allocs), (ctx, c))) w) :=
  fun H0 => proper_entails_meq _ ((interp_fair_read_value sch n ts i a value K st h allocs ctx c
    H0))

theorem x_csl_fair_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i) st
      ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_read_missing sch n ts i a K st h allocs ctx c H0)).trans
    (qnext_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem u_csl_fair_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i)
      st ((h, allocs), (ctx, c))) w ↔ Q (.stuck : TW) w) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_read_missing sch n ts i a K st h allocs ctx c H0)).trans
    (quntil_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem ag_csl_fair_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    h a = none → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i)
      st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_read_missing sch n ts i a K st h allocs ctx c
    H0)).trans (⟨fun h => ag_stuck h, False.elim⟩)

theorem eg_csl_fair_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    h a = none → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i)
      st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_read_missing sch n ts i a K st h allocs ctx c
    H0)).trans (⟨fun h => eg_stuck h, False.elim⟩)

theorem x_csl_fair_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a ≠ none → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ P (log (.inl (CSLObs.heap (upd h a value,
      allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ())))
      (some i) st ((upd h a value, allocs), (ctx, c))) w ∧ Q (FAIR (n + 1) (ts.set i (K (some
      ()))) (some i) st ((upd h a value, allocs), (ctx, c))) (World.obs (E := WR) (.inl
      (CSLObs.heap (upd h a value, allocs))) ⟨⟩)) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_write_present sch n ts i a value K st h allocs ctx c
    H0)).trans (qnext_log_iff hlive)

theorem u_csl_fair_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a ≠ none → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ Q (log (.inl (CSLObs.heap (upd h a value,
      allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ())))
      (some i) st ((upd h a value, allocs), (ctx, c))) w ∨ (P (log (.inl (CSLObs.heap (upd h a
      value, allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some
      ()))) (some i) st ((upd h a value, allocs), (ctx, c))) w ∧ quntil q P Q (FAIR (n + 1)
      (ts.set i (K (some ()))) (some i) st ((upd h a value, allocs), (ctx, c))) (World.obs (E :=
      WR) (.inl (CSLObs.heap (upd h a value, allocs))) ⟨⟩))) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_write_present sch n ts i a value K st h allocs ctx c
    H0)).trans (quntil_log_iff hlive)

theorem ag_csl_fair_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    h a ≠ none → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ entails φ (log (.inl (CSLObs.heap (upd h a value,
      allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ())))
      (some i) st ((upd h a value, allocs), (ctx, c))) w ∧ entails (AG φ) (FAIR (n + 1) (ts.set
      i (K (some ()))) (some i) st ((upd h a value, allocs), (ctx, c))) (World.obs (E := WR)
      (.inl (CSLObs.heap (upd h a value, allocs))) ⟨⟩)) :=
  fun H0 => (proper_entails_meq _ (interp_fair_write_present sch n ts i a value K st h allocs
    ctx c H0)).trans (ag_log_iff)

theorem eg_csl_fair_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    h a ≠ none → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ entails φ (log (.inl (CSLObs.heap (upd h a value,
      allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ())))
      (some i) st ((upd h a value, allocs), (ctx, c))) w ∧ entails (EG φ) (FAIR (n + 1) (ts.set
      i (K (some ()))) (some i) st ((upd h a value, allocs), (ctx, c))) (World.obs (E := WR)
      (.inl (CSLObs.heap (upd h a value, allocs))) ⟨⟩)) :=
  fun H0 => (proper_entails_meq _ (interp_fair_write_present sch n ts i a value K st h allocs
    ctx c H0)).trans (eg_log_iff)

theorem x_csl_fair_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_write_missing sch n ts i a value K st h allocs ctx c
    H0)).trans (qnext_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem u_csl_fair_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ Q (.stuck : TW) w) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_write_missing sch n ts i a value K st h allocs ctx c
    H0)).trans (quntil_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem ag_csl_fair_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    h a = none → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_write_missing sch n ts i a value K st h allocs
    ctx c H0)).trans (⟨fun h => ag_stuck h, False.elim⟩)

theorem eg_csl_fair_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    h a = none → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
      (some i) st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_write_missing sch n ts i a value K st h allocs
    ctx c H0)).trans (⟨fun h => eg_stuck h, False.elim⟩)

theorem x_csl_fair_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (tag value : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ P (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat ×
      Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory, (ctx,
      c + 1))) w ∧ Q (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory, (ctx, c + 1)))
      (World.obs (E := WR) (.inl (CSLObs.emit (stamp (tag, value) c))) ⟨⟩) :=
  (qnext_sb hP hQ (interp_fair_emit_log sch n ts i tag value K st memory ctx c)).trans
    (qnext_log_iff hlive)

theorem u_csl_fair_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (tag value : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ Q (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat ×
      Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory, (ctx,
      c + 1))) w ∨ (P (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs (Nat × Nat) ⊕
      Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory, (ctx, c +
      1))) w ∧ quntil q P Q (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory, (ctx, c
      + 1))) (World.obs (E := WR) (.inl (CSLObs.emit (stamp (tag, value) c))) ⟨⟩)) :=
  (quntil_sb hP hQ (interp_fair_emit_log sch n ts i tag value K st memory ctx c)).trans
    (quntil_log_iff hlive)

theorem eg_csl_fair_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (tag value : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails φ (log (.inl (CSLObs.emit (stamp (tag, value) c)) : CSLObs
      (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory,
      (ctx, c + 1))) w ∧ entails (EG φ) (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st
      (memory, (ctx, c + 1))) (World.obs (E := WR) (.inl (CSLObs.emit (stamp (tag, value) c)))
      ⟨⟩) :=
  (proper_entails_meq _ (interp_fair_emit_log sch n ts i tag value K st memory ctx c)).trans
    (eg_log_iff)

theorem x_csl_fair_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (child : CProg Unit)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.fork child) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ qnext q P Q (FAIR (n + 2) (Vector.cons (denote_flow child >>= fun _ => K
      none) (ts.set i (K (some ())))) (some i.succ) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (interp_fair_fork sch n ts i child K st (memory, (ctx, c)))

theorem u_csl_fair_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (child : CProg Unit)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.fork child) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ quntil q P Q (FAIR (n + 2) (Vector.cons (denote_flow child >>= fun _ => K
      none) (ts.set i (K (some ())))) (some i.succ) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (interp_fair_fork sch n ts i child K st (memory, (ctx, c)))

theorem ag_csl_fair_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (child : CProg Unit)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.fork child) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 2) (Vector.cons (denote_flow child >>=
      fun _ => K none) (ts.set i (K (some ())))) (some i.succ) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (interp_fair_fork sch n ts i child K st (memory, (ctx, c)))

theorem eg_csl_fair_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (child : CProg Unit)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.fork child) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 2) (Vector.cons (denote_flow child >>=
      fun _ => K none) (ts.set i (K (some ())))) (some i.succ) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (interp_fair_fork sch n ts i child K st (memory, (ctx, c)))

theorem x_csl_fair_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (x : A)
    (K : Option A → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) st (memory, (ctx,
      c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (K (some x))) (some i) st (memory, (ctx, c)))
      w :=
  qnext_sb hP hQ (sb_eq (interp_fair_ret sch n ts i x K st (memory, (ctx, c))))

theorem u_csl_fair_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (x : A)
    (K : Option A → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (K (some x))) (some i) st (memory,
      (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_ret sch n ts i x K st (memory, (ctx, c))))

theorem ag_csl_fair_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (x : A)
    (K : Option A → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (K (some x))) (some i) st (memory,
      (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_ret sch n ts i x K st (memory, (ctx, c))))

theorem eg_csl_fair_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (x : A)
    (K : Option A → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (K (some x))) (some i) st (memory,
      (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_ret sch n ts i x K st (memory, (ctx, c))))

theorem x_csl_fair_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow p >>= fun flow =>
      (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) st
      (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_bind sch n ts i p next K st (memory, (ctx, c))))

theorem u_csl_fair_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow p >>= fun flow
      => (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) st
      (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_bind sch n ts i p next K st (memory, (ctx, c))))

theorem ag_csl_fair_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow p >>= fun flow
      => (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) st
      (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_bind sch n ts i p next K st (memory, (ctx, c))))

theorem eg_csl_fair_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow p >>= fun flow
      => (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) st
      (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_bind sch n ts i p next K st (memory, (ctx, c))))

theorem x_csl_fair_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → 0 < base → block_free h base size → (∀ j, 0 < j → j < base → ¬ block_free h j
      size) → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i)
      st ((h, allocs), (ctx, c))) w ↔ P (log (.inl (CSLObs.heap (managed_alloc (h, allocs) base
      size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some base)))
      (some i) st (managed_alloc (h, allocs) base size, (ctx, c))) w ∧ Q (FAIR (n + 1) (ts.set i
      (K (some base))) (some i) st (managed_alloc (h, allocs) base size, (ctx, c))) (World.obs
      (E := WR) (.inl (CSLObs.heap (managed_alloc (h, allocs) base size))) ⟨⟩)) :=
  fun H0 H1 H2 H3 => (qnext_sb hP hQ (interp_fair_alloc_first sch n ts i size base K st h allocs ctx
    c H0 H1 H2 H3)).trans (qnext_log_iff hlive)

theorem u_csl_fair_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → 0 < base → block_free h base size → (∀ j, 0 < j → j < base → ¬ block_free h j
      size) → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some i)
      st ((h, allocs), (ctx, c))) w ↔ Q (log (.inl (CSLObs.heap (managed_alloc (h, allocs) base
      size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some base)))
      (some i) st (managed_alloc (h, allocs) base size, (ctx, c))) w ∨ (P (log (.inl
      (CSLObs.heap (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _
      => FAIR (n + 1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base
      size, (ctx, c))) w ∧ quntil q P Q (FAIR (n + 1) (ts.set i (K (some base))) (some i) st
      (managed_alloc (h, allocs) base size, (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap
      (managed_alloc (h, allocs) base size))) ⟨⟩))) :=
  fun H0 H1 H2 H3 => (quntil_sb hP hQ (interp_fair_alloc_first sch n ts i size base K st h allocs
    ctx c H0 H1 H2 H3)).trans (quntil_log_iff hlive)

theorem ag_csl_fair_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    0 < size → 0 < base → block_free h base size → (∀ j, 0 < j → j < base → ¬ block_free h j
      size) → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some
      i) st ((h, allocs), (ctx, c))) w ↔ entails φ (log (.inl (CSLObs.heap (managed_alloc (h,
      allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K
      (some base))) (some i) st (managed_alloc (h, allocs) base size, (ctx, c))) w ∧ entails (AG
      φ) (FAIR (n + 1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base
      size, (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap (managed_alloc (h, allocs) base
      size))) ⟨⟩)) :=
  fun H0 H1 H2 H3 => (proper_entails_meq _ (interp_fair_alloc_first sch n ts i size base K st h
    allocs ctx c H0 H1 H2 H3)).trans (ag_log_iff)

theorem eg_csl_fair_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    0 < size → 0 < base → block_free h base size → (∀ j, 0 < j → j < base → ¬ block_free h j
      size) → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.alloc size) >>= K)) (some
      i) st ((h, allocs), (ctx, c))) w ↔ entails φ (log (.inl (CSLObs.heap (managed_alloc (h,
      allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K
      (some base))) (some i) st (managed_alloc (h, allocs) base size, (ctx, c))) w ∧ entails (EG
      φ) (FAIR (n + 1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base
      size, (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap (managed_alloc (h, allocs) base
      size))) ⟨⟩)) :=
  fun H0 H1 H2 H3 => (proper_entails_meq _ (interp_fair_alloc_first sch n ts i size base K st h
    allocs ctx c H0 H1 H2 H3)).trans (eg_log_iff)

theorem x_csl_fair_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    heap_finite h → 0 < size → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.alloc size)
      >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ ∀ base, 0 < base → block_free h base size
      → (∀ j, 0 < j → j < base → ¬ block_free h j size) → (P (log (.inl (CSLObs.heap
      (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n +
      1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base size, (ctx, c)))
      w ∧ Q (FAIR (n + 1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base
      size, (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap (managed_alloc (h, allocs) base
      size))) ⟨⟩))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfirst =>
    x_csl_fair_alloc_first sch n ts i size base K st h allocs ctx c w q P Q hP hlive hQ hpos hb hf
      hfirst

theorem u_csl_fair_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    heap_finite h → 0 < size → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.alloc size)
      >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ ∀ base, 0 < base → block_free h base size
      → (∀ j, 0 < j → j < base → ¬ block_free h j size) → (Q (log (.inl (CSLObs.heap
      (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n +
      1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base size, (ctx, c)))
      w ∨ (P (log (.inl (CSLObs.heap (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat)
      ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some base))) (some i) st (managed_alloc (h,
      allocs) base size, (ctx, c))) w ∧ quntil q P Q (FAIR (n + 1) (ts.set i (K (some base)))
      (some i) st (managed_alloc (h, allocs) base size, (ctx, c))) (World.obs (E := WR) (.inl
      (CSLObs.heap (managed_alloc (h, allocs) base size))) ⟨⟩)))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfirst =>
    u_csl_fair_alloc_first sch n ts i size base K st h allocs ctx c w q P Q hP hlive hQ hpos hb hf
      hfirst

theorem ag_csl_fair_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    heap_finite h → 0 < size → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.alloc
      size) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ ∀ base, 0 < base → block_free h
      base size → (∀ j, 0 < j → j < base → ¬ block_free h j size) → (entails φ (log (.inl
      (CSLObs.heap (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _
      => FAIR (n + 1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base
      size, (ctx, c))) w ∧ entails (AG φ) (FAIR (n + 1) (ts.set i (K (some base))) (some i) st
      (managed_alloc (h, allocs) base size, (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap
      (managed_alloc (h, allocs) base size))) ⟨⟩))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfirst =>
    ag_csl_fair_alloc_first sch n ts i size base K st h allocs ctx c w φ hpos hb hf hfirst

theorem eg_csl_fair_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (size : Nat)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    heap_finite h → 0 < size → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.alloc
      size) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ ∀ base, 0 < base → block_free h
      base size → (∀ j, 0 < j → j < base → ¬ block_free h j size) → (entails φ (log (.inl
      (CSLObs.heap (managed_alloc (h, allocs) base size)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _
      => FAIR (n + 1) (ts.set i (K (some base))) (some i) st (managed_alloc (h, allocs) base
      size, (ctx, c))) w ∧ entails (EG φ) (FAIR (n + 1) (ts.set i (K (some base))) (some i) st
      (managed_alloc (h, allocs) base size, (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap
      (managed_alloc (h, allocs) base size))) ⟨⟩))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfirst =>
    eg_csl_fair_alloc_first sch n ts i size base K st h allocs ctx c w φ hpos hb hf hfirst

theorem x_csl_fair_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K)) (some i) st ((h,
      allocs), (ctx, c))) w ↔ False :=
  (qnext_sb hP hQ (interp_fair_alloc_zero sch n ts i K st h allocs ctx c)).trans (qnext_dead_iff
    (fun _ _ tr => ktrans_stuck tr))

theorem u_csl_fair_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K)) (some i) st ((h,
      allocs), (ctx, c))) w ↔ Q (.stuck : TW) w :=
  (quntil_sb hP hQ (interp_fair_alloc_zero sch n ts i K st h allocs ctx c)).trans (quntil_dead_iff
    (fun _ _ tr => ktrans_stuck tr))

theorem ag_csl_fair_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K)) (some i) st ((h,
      allocs), (ctx, c))) w ↔ False :=
  (proper_entails_meq _ (interp_fair_alloc_zero sch n ts i K st h allocs ctx c)).trans (⟨fun h
    => ag_stuck h, False.elim⟩)

theorem eg_csl_fair_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K)) (some i) st ((h,
      allocs), (ctx, c))) w ↔ False :=
  (proper_entails_meq _ (interp_fair_alloc_zero sch n ts i K st h allocs ctx c)).trans (⟨fun h
    => eg_stuck h, False.elim⟩)

theorem x_csl_fair_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) → (qnext q P Q (FAIR (n + 1)
      (ts.set i (denote_flow (.alloc size) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔
      False) :=
  fun H0 H1 => (qnext_sb hP hQ (interp_fair_alloc_no_space sch n ts i size K st h allocs ctx c H0
    H1)).trans (qnext_dead_iff (spin_no_ktrans))

theorem u_csl_fair_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) → (quntil q P Q (FAIR (n + 1)
      (ts.set i (denote_flow (.alloc size) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ Q
      (CTree.spin : TW) w) :=
  fun H0 H1 => (quntil_sb hP hQ (interp_fair_alloc_no_space sch n ts i size K st h allocs ctx c H0
    H1)).trans (quntil_dead_iff (spin_no_ktrans))

theorem ag_csl_fair_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) → (entails (AG φ) (FAIR (n + 1)
      (ts.set i (denote_flow (.alloc size) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔
      False) :=
  fun H0 H1 => (proper_entails_meq _ (interp_fair_alloc_no_space sch n ts i size K st h allocs
    ctx c H0 H1)).trans (⟨ag_spin, False.elim⟩)

theorem eg_csl_fair_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) → (entails (EG φ) (FAIR (n + 1)
      (ts.set i (denote_flow (.alloc size) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔
      False) :=
  fun H0 H1 => (proper_entails_meq _ (interp_fair_alloc_no_space sch n ts i size K st h allocs
    ctx c H0 H1)).trans (⟨eg_spin, False.elim⟩)

theorem x_csl_fair_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory memory' : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = some memory' → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow
      (.free base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ match base with
      | 0 => qnext q P Q (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c)))
        w
      | _ + 1 => P (log (.inl (CSLObs.heap memory') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c))) w ∧ Q (FAIR (n +
        1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c))) (World.obs (E := WR) (.inl
        (CSLObs.heap memory')) ⟨⟩)) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_free sch n ts i base K st memory memory' ctx c H0)).trans
    ((by cases base <;> first | exact Iff.rfl | exact qnext_log_iff hlive))

theorem u_csl_fair_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory memory' : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = some memory' → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow
      (.free base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ match base with
      | 0 => quntil q P Q (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx,
        c))) w
      | _ + 1 => Q (log (.inl (CSLObs.heap memory') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c))) w ∨ (P (log (.inl
        (CSLObs.heap memory') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K
        (some ()))) (some i) st (memory', (ctx, c))) w ∧ quntil q P Q (FAIR (n + 1) (ts.set i (K
        (some ()))) (some i) st (memory', (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap
        memory')) ⟨⟩))) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_free sch n ts i base K st memory memory' ctx c H0)).trans
    ((by cases base <;> first | exact Iff.rfl | exact quntil_log_iff hlive))

theorem ag_csl_fair_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory memory' : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    managed_free memory base = some memory' → (entails (AG φ) (FAIR (n + 1) (ts.set i
      (denote_flow (.free base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ match base with
      | 0 => entails (AG φ) (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx,
        c))) w
      | _ + 1 => entails φ (log (.inl (CSLObs.heap memory') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun
        _ => FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c))) w ∧ entails
        (AG φ) (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c)))
        (World.obs (E := WR) (.inl (CSLObs.heap memory')) ⟨⟩)) :=
  fun H0 => (proper_entails_meq _ (interp_fair_free sch n ts i base K st memory memory' ctx c
    H0)).trans ((by cases base <;> first | exact Iff.rfl | exact ag_log_iff))

theorem eg_csl_fair_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory memory' : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    managed_free memory base = some memory' → (entails (EG φ) (FAIR (n + 1) (ts.set i
      (denote_flow (.free base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ match base with
      | 0 => entails (EG φ) (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx,
        c))) w
      | _ + 1 => entails φ (log (.inl (CSLObs.heap memory') : CSLObs (Nat × Nat) ⊕ Nat) >>= fun
        _ => FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c))) w ∧ entails
        (EG φ) (FAIR (n + 1) (ts.set i (K (some ()))) (some i) st (memory', (ctx, c)))
        (World.obs (E := WR) (.inl (CSLObs.heap memory')) ⟨⟩)) :=
  fun H0 => (proper_entails_meq _ (interp_fair_free sch n ts i base K st memory memory' ctx c
    H0)).trans ((by cases base <;> first | exact Iff.rfl | exact eg_log_iff))

theorem x_csl_fair_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = none → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.free
      base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ False) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_free_invalid sch n ts i base K st memory ctx c H0)).trans
    (qnext_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem u_csl_fair_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = none → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.free
      base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ Q (.stuck : TW) w) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_free_invalid sch n ts i base K st memory ctx c H0)).trans
    (quntil_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem ag_csl_fair_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    managed_free memory base = none → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow
      (.free base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_free_invalid sch n ts i base K st memory ctx c
    H0)).trans (⟨fun h => ag_stuck h, False.elim⟩)

theorem eg_csl_fair_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (base : Nat)
    (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    managed_free memory base = none → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow
      (.free base) >>= K)) (some i) st (memory, (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_free_invalid sch n ts i base K st memory ctx c
    H0)).trans (⟨fun h => eg_stuck h, False.elim⟩)

theorem x_csl_fair_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i)
      st (memory, (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp a >>= fun addr
      => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow
      (.cas (.lit addr) (.lit old) (.lit value)) >>= K)) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_cas_exp sch n ts i a expected desired K st (memory, (ctx, c))))

theorem u_csl_fair_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i)
      st (memory, (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp a >>= fun addr
      => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow
      (.cas (.lit addr) (.lit old) (.lit value)) >>= K)) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ
    (sb_eq (interp_fair_cas_exp sch n ts i a expected desired K st (memory, (ctx, c))))

theorem ag_csl_fair_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some
      i) st (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp a >>= fun
      addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow
      (.cas (.lit addr) (.lit old) (.lit value)) >>= K)) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_cas_exp sch n ts i a expected desired K st (memory,
    (ctx, c))))

theorem eg_csl_fair_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some
      i) st (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp a >>= fun
      addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow
      (.cas (.lit addr) (.lit old) (.lit value)) >>= K)) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_cas_exp sch n ts i a expected desired K st (memory,
    (ctx, c))))

theorem x_csl_fair_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop)
    (hP : SbProper P) (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some current → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a) (.lit
      expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ if current =
      expected then P (log (.inl (CSLObs.heap (upd h a desired, allocs)) : CSLObs (Nat × Nat) ⊕
      Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some true))) (some i) st ((upd h a desired,
      allocs), (ctx, c))) w ∧ Q (FAIR (n + 1) (ts.set i (K (some true))) (some i) st ((upd h a
      desired, allocs), (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap (upd h a desired,
      allocs))) ⟨⟩) else qnext q P Q (FAIR (n + 1) (ts.set i (K (some false))) (some i) st ((h,
      allocs), (ctx, c))) w) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_cas_value sch n ts i a expected desired current K st h
    allocs ctx c H0)).trans ((by by_cases hc : current = expected <;> simp only [hc, ↓reduceIte]
    <;> first | exact Iff.rfl | exact qnext_log_iff hlive))

theorem u_csl_fair_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop)
    (hP : SbProper P) (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some current → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a) (.lit
      expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ if current =
      expected then Q (log (.inl (CSLObs.heap (upd h a desired, allocs)) : CSLObs (Nat × Nat) ⊕
      Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some true))) (some i) st ((upd h a desired,
      allocs), (ctx, c))) w ∨ (P (log (.inl (CSLObs.heap (upd h a desired, allocs)) : CSLObs
      (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some true))) (some i) st ((upd
      h a desired, allocs), (ctx, c))) w ∧ quntil q P Q (FAIR (n + 1) (ts.set i (K (some true)))
      (some i) st ((upd h a desired, allocs), (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap
      (upd h a desired, allocs))) ⟨⟩)) else quntil q P Q (FAIR (n + 1) (ts.set i (K (some
      false))) (some i) st ((h, allocs), (ctx, c))) w) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_cas_value sch n ts i a expected desired current K st h
    allocs ctx c H0)).trans ((by by_cases hc : current = expected <;> simp only [hc, ↓reduceIte]
    <;> first | exact Iff.rfl | exact quntil_log_iff hlive))

theorem ag_csl_fair_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    h a = some current → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a)
      (.lit expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ if
      current = expected then entails φ (log (.inl (CSLObs.heap (upd h a desired, allocs)) :
      CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some true))) (some i) st
      ((upd h a desired, allocs), (ctx, c))) w ∧ entails (AG φ) (FAIR (n + 1) (ts.set i (K (some
      true))) (some i) st ((upd h a desired, allocs), (ctx, c))) (World.obs (E := WR) (.inl
      (CSLObs.heap (upd h a desired, allocs))) ⟨⟩) else entails (AG φ) (FAIR (n + 1) (ts.set i
      (K (some false))) (some i) st ((h, allocs), (ctx, c))) w) :=
  fun H0 => (proper_entails_meq _ (interp_fair_cas_value sch n ts i a expected desired current K
    st h allocs ctx c H0)).trans ((by by_cases hc : current = expected <;> simp only [hc,
    ↓reduceIte] <;> first | exact Iff.rfl | exact ag_log_iff))

theorem eg_csl_fair_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    h a = some current → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a)
      (.lit expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ if
      current = expected then entails φ (log (.inl (CSLObs.heap (upd h a desired, allocs)) :
      CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => FAIR (n + 1) (ts.set i (K (some true))) (some i) st
      ((upd h a desired, allocs), (ctx, c))) w ∧ entails (EG φ) (FAIR (n + 1) (ts.set i (K (some
      true))) (some i) st ((upd h a desired, allocs), (ctx, c))) (World.obs (E := WR) (.inl
      (CSLObs.heap (upd h a desired, allocs))) ⟨⟩) else entails (EG φ) (FAIR (n + 1) (ts.set i
      (K (some false))) (some i) st ((h, allocs), (ctx, c))) w) :=
  fun H0 => (proper_entails_meq _ (interp_fair_cas_value sch n ts i a expected desired current K
    st h allocs ctx c H0)).trans ((by by_cases hc : current = expected <;> simp only [hc,
    ↓reduceIte] <;> first | exact Iff.rfl | exact eg_log_iff))

theorem x_csl_fair_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop)
    (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a) (.lit
      expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_cas_missing sch n ts i a expected desired K st h allocs ctx
    c H0)).trans (qnext_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem u_csl_fair_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop)
    (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a) (.lit
      expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ Q (.stuck : TW)
      w) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_cas_missing sch n ts i a expected desired K st h allocs
    ctx c H0)).trans (quntil_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem ag_csl_fair_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    h a = none → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a) (.lit
      expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_cas_missing sch n ts i a expected desired K st h
    allocs ctx c H0)).trans (⟨fun h => ag_stuck h, False.elim⟩)

theorem eg_csl_fair_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    h a = none → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.cas (.lit a) (.lit
      expected) (.lit desired)) >>= K)) (some i) st ((h, allocs), (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_cas_missing sch n ts i a expected desired K st h
    allocs ctx c H0)).trans (⟨fun h => eg_stuck h, False.elim⟩)

theorem x_csl_fair_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (e : CExp)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.eval e) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value => K (some
      value))) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_source_eval sch n ts i e K st (memory, (ctx, c))))

theorem u_csl_fair_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (e : CExp)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.eval e) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value => K (some
      value))) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_source_eval sch n ts i e K st (memory, (ctx, c))))

theorem ag_csl_fair_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (e : CExp)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.eval e) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value => K
      (some value))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_eval sch n ts i e K st (memory, (ctx, c))))

theorem eg_csl_fair_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (e : CExp)
    (K : Option Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.eval e) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value => K
      (some value))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_eval sch n ts i e K st (memory, (ctx, c))))

theorem x_csl_fair_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (e : CExp) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.assign name e) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value =>
      source_get >>= fun ctx => source_put (Ctx.add name value ctx) >>= fun _ => K (some ())))
      (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_assign sch n ts i name e K st (memory, (ctx, c))))

theorem u_csl_fair_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (e : CExp) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.assign name e) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value
      => source_get >>= fun ctx => source_put (Ctx.add name value ctx) >>= fun _ => K (some
      ()))) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_assign sch n ts i name e K st (memory, (ctx, c))))

theorem ag_csl_fair_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (e : CExp) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.assign name e) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value
      => source_get >>= fun ctx => source_put (Ctx.add name value ctx) >>= fun _ => K (some
      ()))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_assign sch n ts i name e K st (memory, (ctx, c))))

theorem eg_csl_fair_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (e : CExp) (K : Option Unit → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.assign name e) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp e >>= fun value
      => source_get >>= fun ctx => source_put (Ctx.add name value ctx) >>= fun _ => K (some
      ()))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_assign sch n ts i name e K st (memory, (ctx, c))))

theorem x_csl_fair_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp test >>= fun value
      => if is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (some i) st
      (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_source_if sch n ts i test yes no K st (memory, (ctx, c))))

theorem u_csl_fair_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp test >>= fun
      value => if is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (some i)
      st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_source_if sch n ts i test yes no K st (memory, (ctx, c))))

theorem ag_csl_fair_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp test >>= fun
      value => if is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (some i)
      st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_if sch n ts i test yes no K st (memory, (ctx,
    c))))

theorem eg_csl_fair_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp test >>= fun
      value => if is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (some i)
      st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_if sch n ts i test yes no K st (memory, (ctx,
    c))))

theorem x_csl_fair_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow body >>=
      until_tail body K)) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_until_none sch n ts i body K st (memory, (ctx, c))))

theorem u_csl_fair_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow body >>=
      until_tail body K)) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_until_none sch n ts i body K st (memory, (ctx, c))))

theorem ag_csl_fair_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR)
    (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow body >>=
      until_tail body K)) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_until_none sch n ts i body K st (memory, (ctx, c))))

theorem eg_csl_fair_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR)
    (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow body >>=
      until_tail body K)) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_until_none sch n ts i body K st (memory, (ctx, c))))

theorem x_csl_fair_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (test : CExp)
    (body : CProg Unit) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_flow (.while test body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp test >>= fun value
      => if is_true value then denote_flow body >>= fun flow =>
      (match flow with | none => K none | some _ => .guard (denote_flow (.while test body) >>= K))
      else K (some ()))) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_while_unfold sch n ts i test body K st (memory, (ctx, c))))

theorem u_csl_fair_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (test : CExp)
    (body : CProg Unit) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_flow (.while test body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp test >>= fun
      value => if is_true value then denote_flow body >>= fun flow =>
      (match flow with | none => K none | some _ => .guard (denote_flow (.while test body) >>= K))
      else K (some ()))) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_while_unfold sch n ts i test body K st (memory, (ctx, c))))

theorem ag_csl_fair_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_flow (.while test body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp test >>= fun
      value => if is_true value then denote_flow body >>= fun flow =>
      (match flow with | none => K none | some _ => .guard (denote_flow (.while test body) >>= K))
      else K (some ()))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_while_unfold sch n ts i test body K st (memory, (ctx,
    c))))

theorem eg_csl_fair_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_flow (.while test body) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp test >>= fun
      value => if is_true value then denote_flow body >>= fun flow =>
      (match flow with | none => K none | some _ => .guard (denote_flow (.while test body) >>= K))
      else K (some ()))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_while_unfold sch n ts i test body K st (memory, (ctx,
    c))))

theorem x_csl_fair_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (value : Nat)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp (.lit value) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (K value)) (some i) st (memory, (ctx,
      c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_lit sch n ts i value K st (memory, (ctx, c))))

theorem u_csl_fair_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (value : Nat)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp (.lit value) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (K value)) (some i) st (memory, (ctx,
      c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_lit sch n ts i value K st (memory, (ctx, c))))

theorem ag_csl_fair_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (value : Nat)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp (.lit value) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (K value)) (some i) st (memory,
      (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_lit sch n ts i value K st (memory, (ctx, c))))

theorem eg_csl_fair_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (value : Nat)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp (.lit value) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (K value)) (some i) st (memory,
      (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_lit sch n ts i value K st (memory, (ctx, c))))

theorem x_csl_fair_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = none → (qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp (.var name)
      >>= K)) (some i) st (memory, (ctx, c))) w ↔ False) :=
  fun H0 => (qnext_sb hP hQ (interp_fair_var_missing sch n ts i name K st (memory, (ctx, c))
    H0)).trans (qnext_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem u_csl_fair_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = none → (quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp (.var name)
      >>= K)) (some i) st (memory, (ctx, c))) w ↔ Q (.stuck : TW) w) :=
  fun H0 => (quntil_sb hP hQ (interp_fair_var_missing sch n ts i name K st (memory, (ctx, c))
    H0)).trans (quntil_dead_iff (fun _ _ tr => ktrans_stuck tr))

theorem ag_csl_fair_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    Ctx.lookup name ctx = none → (entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp (.var name)
      >>= K)) (some i) st (memory, (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_var_missing sch n ts i name K st (memory, (ctx,
    c)) H0)).trans (⟨fun h => ag_stuck h, False.elim⟩)

theorem eg_csl_fair_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) :
    Ctx.lookup name ctx = none → (entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp (.var name)
      >>= K)) (some i) st (memory, (ctx, c))) w ↔ False) :=
  fun H0 => (proper_entails_meq _ (interp_fair_var_missing sch n ts i name K st (memory, (ctx,
    c)) H0)).trans (⟨fun h => eg_stuck h, False.elim⟩)

theorem x_csl_fair_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x => denote_exp
      eb >>= fun y => K (x + y))) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_source_exp_plus sch n ts i ea eb K st (memory, (ctx, c))))

theorem u_csl_fair_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x => denote_exp
      eb >>= fun y => K (x + y))) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_source_exp_plus sch n ts i ea eb K st (memory, (ctx, c))))

theorem ag_csl_fair_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x =>
      denote_exp eb >>= fun y => K (x + y))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_exp_plus sch n ts i ea eb K st (memory, (ctx,
    c))))

theorem eg_csl_fair_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x =>
      denote_exp eb >>= fun y => K (x + y))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_exp_plus sch n ts i ea eb K st (memory, (ctx,
    c))))

theorem x_csl_fair_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x => denote_exp
      eb >>= fun y => K (x - y))) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_source_exp_minus sch n ts i ea eb K st (memory, (ctx, c))))

theorem u_csl_fair_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x => denote_exp
      eb >>= fun y => K (x - y))) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_source_exp_minus sch n ts i ea eb K st (memory, (ctx, c))))

theorem ag_csl_fair_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x =>
      denote_exp eb >>= fun y => K (x - y))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_exp_minus sch n ts i ea eb K st (memory, (ctx,
    c))))

theorem eg_csl_fair_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x =>
      denote_exp eb >>= fun y => K (x - y))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_exp_minus sch n ts i ea eb K st (memory, (ctx,
    c))))

theorem x_csl_fair_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ qnext q P Q (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x => denote_exp
      eb >>= fun y => K (x * y))) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ (sb_eq (interp_fair_source_exp_mult sch n ts i ea eb K st (memory, (ctx, c))))

theorem u_csl_fair_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K)) (some i) st (memory,
      (ctx, c))) w ↔ quntil q P Q (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x => denote_exp
      eb >>= fun y => K (x * y))) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ (sb_eq (interp_fair_source_exp_mult sch n ts i ea eb K st (memory, (ctx, c))))

theorem ag_csl_fair_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (AG φ) (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x =>
      denote_exp eb >>= fun y => K (x * y))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_exp_mult sch n ts i ea eb K st (memory, (ctx,
    c))))

theorem eg_csl_fair_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (ea eb : CExp)
    (K : Nat → Thread sE Bn) (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K)) (some i) st
      (memory, (ctx, c))) w ↔ entails (EG φ) (FAIR (n + 1) (ts.set i (denote_exp ea >>= fun x =>
      denote_exp eb >>= fun y => K (x * y))) (some i) st (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_source_exp_mult sch n ts i ea eb K st (memory, (ctx,
    c))))

theorem x_csl_fair_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (t : Thread sE Bn)
    (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    qnext q P Q (FAIR (n + 1) (ts.set i (.guard t)) (some i) st (memory, (ctx, c))) w ↔ qnext q
      P Q (FAIR (n + 1) (ts.set i (t)) (some i) st (memory, (ctx, c))) w :=
  qnext_sb hP hQ ((interp_fair_source_guard sch n ts i t st (memory, (ctx, c))))

theorem u_csl_fair_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (t : Thread sE Bn)
    (st : sch.sched_state) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (FAIR (n + 1) (ts.set i (.guard t)) (some i) st (memory, (ctx, c))) w ↔ quntil
      q P Q (FAIR (n + 1) (ts.set i (t)) (some i) st (memory, (ctx, c))) w :=
  quntil_sb hP hQ ((interp_fair_source_guard sch n ts i t st (memory, (ctx, c))))

end FairKernel

/-! ## Round-robin scheduling points -/

theorem x_csl_rr_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    (qnext q P Q (RR (n + 1) (ts.set i (denote_flow .yield >>= K)) (some i) m (memory, (ctx,
      c))) w ↔ P (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ => RR (n + 1)
      (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧ Q (RR (n +
      1) (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) (World.obs (E
      := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩)) := by
  rw [qnext_sb hP hQ (sbisim_trans (interp_rr_yield n ts i K m (memory, (ctx, c)))
    (interp_schedule_rr_select sh n _ m _)), qnext_vis_iff (E := WR) ⟨⟩ hlive]
  cases q
  · exact and_congr_right fun _ => ⟨fun h => h ⟨⟩, fun h _ => h⟩
  · exact and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩

theorem u_csl_rr_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    (quntil q P Q (RR (n + 1) (ts.set i (denote_flow .yield >>= K)) (some i) m (memory, (ctx,
      c))) w ↔ Q (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ => RR (n + 1)
      (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∨ (P
      (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ => RR (n + 1) (ts.set i (K
      (some ()))) (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧ quntil q P Q (RR (n + 1)
      (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) (World.obs (E :=
      WR) (.inr (slot_index (rr_pick n m))) ⟨⟩))) := by
  rw [quntil_sb hP hQ (sbisim_trans (interp_rr_yield n ts i K m (memory, (ctx, c)))
    (interp_schedule_rr_select sh n _ m _)), quntil_unfold, qnext_vis_iff (E := WR) ⟨⟩ hlive]
  cases q
  · exact or_congr_right (and_congr_right fun _ => ⟨fun h => h ⟨⟩, fun h _ => h⟩)
  · exact or_congr_right (and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩)

theorem eg_csl_rr_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    (entails (EG φ) (RR (n + 1) (ts.set i (denote_flow .yield >>= K)) (some i) m (memory, (ctx,
      c))) w ↔ entails φ (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ => RR (n +
      1) (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧ entails
      (EG φ) (RR (n + 1) (ts.set i (K (some ()))) (some (rr_pick n m)) (m + 1) (memory, (ctx,
      c))) (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩)) :=
  (proper_entails_meq _ (interp_rr_yield n ts i K m (memory, (ctx, c)))).trans
    (eg_csl_rr_select ..)

theorem x_csl_rr_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (value : Nat) (K : Nat → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = some value → (qnext q P Q (RR (n + 1) (ts.set i (denote_exp (.var
      name) >>= K)) (some i) m (memory, (ctx, c))) w ↔ P (CTree.vis (E := WR) (.inr (slot_index
      (rr_pick n m))) fun _ => RR (n + 1) (ts.set i (K value)) (some (rr_pick n m)) (m + 1)
      (memory, (ctx, c))) w ∧ Q (RR (n + 1) (ts.set i (K value)) (some (rr_pick n m)) (m + 1)
      (memory, (ctx, c))) (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩)) := by
  intro H
  rw [qnext_sb hP hQ (sbisim_trans (interp_rr_var n ts i name value K m (memory, (ctx, c)) H)
    (interp_schedule_rr_select sh n _ m _)), qnext_vis_iff (E := WR) ⟨⟩ hlive]
  cases q
  · exact and_congr_right fun _ => ⟨fun h => h ⟨⟩, fun h _ => h⟩
  · exact and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩

theorem u_csl_rr_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (value : Nat) (K : Nat → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = some value → (quntil q P Q (RR (n + 1) (ts.set i (denote_exp (.var
      name) >>= K)) (some i) m (memory, (ctx, c))) w ↔ Q (CTree.vis (E := WR) (.inr (slot_index
      (rr_pick n m))) fun _ => RR (n + 1) (ts.set i (K value)) (some (rr_pick n m)) (m + 1)
      (memory, (ctx, c))) w ∨ (P (CTree.vis (E := WR) (.inr (slot_index (rr_pick n m))) fun _ =>
      RR (n + 1) (ts.set i (K value)) (some (rr_pick n m)) (m + 1) (memory, (ctx, c))) w ∧
      quntil q P Q (RR (n + 1) (ts.set i (K value)) (some (rr_pick n m)) (m + 1) (memory, (ctx,
      c))) (World.obs (E := WR) (.inr (slot_index (rr_pick n m))) ⟨⟩))) := by
  intro H
  rw [quntil_sb hP hQ (sbisim_trans (interp_rr_var n ts i name value K m (memory, (ctx, c)) H)
    (interp_schedule_rr_select sh n _ m _)), quntil_unfold, qnext_vis_iff (E := WR) ⟨⟩ hlive]
  cases q
  · exact or_congr_right (and_congr_right fun _ => ⟨fun h => h ⟨⟩, fun h _ => h⟩)
  · exact or_congr_right (and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩)

theorem ag_csl_rr_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (value : Nat) (K : Nat → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    Ctx.lookup name ctx = some value → (entails (AG φ) (RR (n + 1) (ts.set i (denote_exp (.var
      name) >>= K)) (some i) m (memory, (ctx, c))) w ↔ entails φ (CTree.vis (E := WR) (.inr
      (slot_index (rr_pick n m))) fun _ => RR (n + 1) (ts.set i (K value)) (some (rr_pick n m))
      (m + 1) (memory, (ctx, c))) w ∧ entails (AG φ) (RR (n + 1) (ts.set i (K value)) (some
      (rr_pick n m)) (m + 1) (memory, (ctx, c))) (World.obs (E := WR) (.inr (slot_index (rr_pick
      n m))) ⟨⟩)) :=
  fun H => (proper_entails_meq _ (interp_rr_var n ts i name value K m (memory, (ctx, c))
    H)).trans (ag_csl_rr_select ..)

theorem eg_csl_rr_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (name : String)
    (value : Nat) (K : Nat → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (φ : TiclL WR) :
    Ctx.lookup name ctx = some value → (entails (EG φ) (RR (n + 1) (ts.set i (denote_exp (.var
      name) >>= K)) (some i) m (memory, (ctx, c))) w ↔ entails φ (CTree.vis (E := WR) (.inr
      (slot_index (rr_pick n m))) fun _ => RR (n + 1) (ts.set i (K value)) (some (rr_pick n m))
      (m + 1) (memory, (ctx, c))) w ∧ entails (EG φ) (RR (n + 1) (ts.set i (K value)) (some
      (rr_pick n m)) (m + 1) (memory, (ctx, c))) (World.obs (E := WR) (.inr (slot_index (rr_pick
      n m))) ⟨⟩)) :=
  fun H => (proper_entails_meq _ (interp_rr_var n ts i name value K m (memory, (ctx, c))
    H)).trans (eg_csl_rr_select ..)

/-! ## Round-robin instances used downstream -/

theorem x_csl_rr_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (m : Nat)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    qnext q P Q (RR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) m (memory,
      (ctx, c))) w ↔ qnext q P Q (RR (n + 1) (ts.set i (denote_flow p >>= fun flow =>
      (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) m
      (memory, (ctx, c))) w :=
  x_csl_fair_bind rr_scheduler n ts i p next K m memory ctx c w q P Q hP _hlive hQ

theorem x_csl_rr_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Unit → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a ≠ none → (qnext q P Q (RR (n + 1) (ts.set i (denote_flow (.write a value) >>= K)) (some
      i) m ((h, allocs), (ctx, c))) w ↔ P (log (.inl (CSLObs.heap (upd h a value, allocs)) :
      CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => RR (n + 1) (ts.set i (K (some ()))) (some i) m
      ((upd h a value, allocs), (ctx, c))) w ∧ Q (RR (n + 1) (ts.set i (K (some ()))) (some i) m
      ((upd h a value, allocs), (ctx, c))) (World.obs (E := WR) (.inl (CSLObs.heap (upd h a
      value, allocs))) ⟨⟩)) :=
  x_csl_fair_write rr_scheduler n ts i a value K m h allocs ctx c w q P Q hP hlive hQ

theorem u_csl_rr_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (m : Nat)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (RR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) m (memory,
      (ctx, c))) w ↔ quntil q P Q (RR (n + 1) (ts.set i (denote_flow p >>= fun flow =>
      (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) m
      (memory, (ctx, c))) w :=
  u_csl_fair_bind rr_scheduler n ts i p next K m memory ctx c w q P Q hP _hlive hQ

theorem u_csl_rr_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (t : Thread sE Bn)
    (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (q : Ticlq)
    (P Q : TW → World WR → Prop) (hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (hQ : SbProper Q) :
    quntil q P Q (RR (n + 1) (ts.set i (.guard t)) (some i) m (memory, (ctx, c))) w ↔ quntil q P
      Q (RR (n + 1) (ts.set i (t)) (some i) m (memory, (ctx, c))) w :=
  u_csl_fair_guard rr_scheduler n ts i t m memory ctx c w q P Q hP _hlive hQ

theorem u_csl_rr_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (x : A)
    (K : Option A → Thread sE Bn) (m : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (RR (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) m (memory, (ctx,
      c))) w ↔ quntil q P Q (RR (n + 1) (ts.set i (K (some x))) (some i) m (memory, (ctx, c))) w :=
  u_csl_fair_ret rr_scheduler n ts i x K m memory ctx c w q P Q hP _hlive hQ

theorem u_csl_rr_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (a value : Nat)
    (K : Option Unit → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WR) (q : Ticlq) (P Q : TW → World WR → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a ≠ none → (quntil q P Q (RR (n + 1) (ts.set i (denote_flow (.write a value) >>= K)) (some
      i) m ((h, allocs), (ctx, c))) w ↔ Q (log (.inl (CSLObs.heap (upd h a value, allocs)) :
      CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => RR (n + 1) (ts.set i (K (some ()))) (some i) m
      ((upd h a value, allocs), (ctx, c))) w ∨ (P (log (.inl (CSLObs.heap (upd h a value,
      allocs)) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => RR (n + 1) (ts.set i (K (some ())))
      (some i) m ((upd h a value, allocs), (ctx, c))) w ∧ quntil q P Q (RR (n + 1) (ts.set i (K
      (some ()))) (some i) m ((upd h a value, allocs), (ctx, c))) (World.obs (E := WR) (.inl
      (CSLObs.heap (upd h a value, allocs))) ⟨⟩))) :=
  u_csl_fair_write rr_scheduler n ts i a value K m h allocs ctx c w q P Q hP hlive hQ

theorem au_csl_rr_bind {ix : Option Type} {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (m : Nat)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR ix) :
    entails (φ AU ψ) (RR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) m
      (memory, (ctx, c))) w ↔ entails (φ AU ψ) (RR (n + 1) (ts.set i (denote_flow p >>= fun flow
      => (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) m
      (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_bind rr_scheduler n ts i p next K m (memory, (ctx,
    c))))

theorem au_csl_rr_fork {ix : Option Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (child : CProg Unit) (K : Option Unit → Thread sE Bn) (m : Nat) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR ix) :
    entails (φ AU ψ) (RR (n + 1) (ts.set i (denote_flow (.fork child) >>= K)) (some i) m
      (memory, (ctx, c))) w ↔ entails (φ AU ψ) (RR (n + 2) (Vector.cons (denote_flow child >>=
      fun _ => K none) (ts.set i (K (some ())))) (some i.succ) m (memory, (ctx, c))) w :=
  proper_entails_meq _ (interp_fair_fork rr_scheduler n ts i child K m (memory, (ctx, c)))

theorem au_csl_rr_ret {ix : Option Type} {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (x : A) (K : Option A → Thread sE Bn) (m : Nat) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR ix) :
    entails (φ AU ψ) (RR (n + 1) (ts.set i (denote_flow (.ret x) >>= K)) (some i) m (memory,
      (ctx, c))) w ↔ entails (φ AU ψ) (RR (n + 1) (ts.set i (K (some x))) (some i) m (memory,
      (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_ret rr_scheduler n ts i x K m (memory, (ctx, c))))

theorem eu_csl_rr_bind {ix : Option Type} {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (m : Nat)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR ix) :
    entails (φ EU ψ) (RR (n + 1) (ts.set i (denote_flow (.bind p next) >>= K)) (some i) m
      (memory, (ctx, c))) w ↔ entails (φ EU ψ) (RR (n + 1) (ts.set i (denote_flow p >>= fun flow
      => (match flow with | none => K none | some x => denote_flow (next x) >>= K))) (some i) m
      (memory, (ctx, c))) w :=
  proper_entails_meq _ (sb_eq (interp_fair_bind rr_scheduler n ts i p next K m (memory, (ctx,
    c))))

theorem eu_csl_rr_read_missing {ix : Option Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (a : Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WR) (φ : TiclL WR) (ψ : Ticl WR ix) :
    h a = none → (entails (φ EU ψ) (RR (n + 1) (ts.set i (denote_flow (.read a) >>= K)) (some i)
      m ((h, allocs), (ctx, c))) w ↔ entails ψ (.stuck : TW) w) :=
  fun H0 => (proper_entails_meq _ (interp_fair_read_missing rr_scheduler n ts i a K m h allocs
    ctx c H0)).trans eu_stuck

end CoCSL

/- Not ported: covered by kernel `x/u/ag/eg_csl_fair_*` (the round-robin instance is the kernel at
`rr_scheduler`; formula modalities are `qnext`/`quntil` at `q := .A/.E` or `proper_entails_meq` with
the `interp_rr_*` equations), the formula-level names being outside the downstream-use set `U`:
  x_csl_rr_read, u_csl_rr_read, an_csl_rr_read, en_csl_rr_read, au_csl_rr_read, eu_csl_rr_read,
  ag_csl_rr_read, eg_csl_rr_read, ax_csl_rr_read, ex_csl_rr_read, af_csl_rr_read, ef_csl_rr_read,
  x_csl_rr_read_missing, u_csl_rr_read_missing, an_csl_rr_read_missing, en_csl_rr_read_missing,
  au_csl_rr_read_missing, ag_csl_rr_read_missing, eg_csl_rr_read_missing, ax_csl_rr_read_missing,
  ex_csl_rr_read_missing, af_csl_rr_read_missing, ef_csl_rr_read_missing, an_csl_rr_write,
  en_csl_rr_write, au_csl_rr_write, eu_csl_rr_write, ag_csl_rr_write, eg_csl_rr_write,
  ax_csl_rr_write, ex_csl_rr_write, af_csl_rr_write, ef_csl_rr_write, x_csl_rr_write_missing,
  u_csl_rr_write_missing, an_csl_rr_write_missing, en_csl_rr_write_missing,
  au_csl_rr_write_missing, eu_csl_rr_write_missing, ag_csl_rr_write_missing,
  eg_csl_rr_write_missing, ax_csl_rr_write_missing, ex_csl_rr_write_missing,
  af_csl_rr_write_missing, ef_csl_rr_write_missing, x_csl_rr_emit, u_csl_rr_emit, en_csl_rr_emit,
  eu_csl_rr_emit, eg_csl_rr_emit, ax_csl_rr_emit, ex_csl_rr_emit, af_csl_rr_emit, ef_csl_rr_emit,
  en_csl_rr_yield, eu_csl_rr_yield, ax_csl_rr_yield, ex_csl_rr_yield, af_csl_rr_yield,
  ef_csl_rr_yield, x_csl_rr_fork, u_csl_rr_fork, an_csl_rr_fork, en_csl_rr_fork, eu_csl_rr_fork,
  ag_csl_rr_fork, eg_csl_rr_fork, ax_csl_rr_fork, ex_csl_rr_fork, af_csl_rr_fork, ef_csl_rr_fork,
  x_csl_rr_ret, an_csl_rr_ret, en_csl_rr_ret, eu_csl_rr_ret, ag_csl_rr_ret, eg_csl_rr_ret,
  ax_csl_rr_ret, ex_csl_rr_ret, af_csl_rr_ret, ef_csl_rr_ret, an_csl_rr_bind, en_csl_rr_bind,
  ag_csl_rr_bind, eg_csl_rr_bind, ax_csl_rr_bind, ex_csl_rr_bind, af_csl_rr_bind, ef_csl_rr_bind,
  x_csl_rr_alloc_first, u_csl_rr_alloc_first, an_csl_rr_alloc_first, en_csl_rr_alloc_first,
  au_csl_rr_alloc_first, eu_csl_rr_alloc_first, ag_csl_rr_alloc_first, eg_csl_rr_alloc_first,
  ax_csl_rr_alloc_first, ex_csl_rr_alloc_first, af_csl_rr_alloc_first, ef_csl_rr_alloc_first,
  x_csl_rr_alloc, u_csl_rr_alloc, an_csl_rr_alloc, en_csl_rr_alloc, au_csl_rr_alloc,
  eu_csl_rr_alloc, ag_csl_rr_alloc, eg_csl_rr_alloc, ax_csl_rr_alloc, ex_csl_rr_alloc,
  af_csl_rr_alloc, ef_csl_rr_alloc, x_csl_rr_alloc_zero, u_csl_rr_alloc_zero, an_csl_rr_alloc_zero,
  en_csl_rr_alloc_zero, au_csl_rr_alloc_zero, eu_csl_rr_alloc_zero, ag_csl_rr_alloc_zero,
  eg_csl_rr_alloc_zero, ax_csl_rr_alloc_zero, ex_csl_rr_alloc_zero, af_csl_rr_alloc_zero,
  ef_csl_rr_alloc_zero, x_csl_rr_alloc_no_space, u_csl_rr_alloc_no_space, an_csl_rr_alloc_no_space,
  en_csl_rr_alloc_no_space, au_csl_rr_alloc_no_space, eu_csl_rr_alloc_no_space,
  ag_csl_rr_alloc_no_space, eg_csl_rr_alloc_no_space, ax_csl_rr_alloc_no_space,
  ex_csl_rr_alloc_no_space, af_csl_rr_alloc_no_space, ef_csl_rr_alloc_no_space, x_csl_rr_free,
  u_csl_rr_free, an_csl_rr_free, en_csl_rr_free, au_csl_rr_free, eu_csl_rr_free, ag_csl_rr_free,
  eg_csl_rr_free, ax_csl_rr_free, ex_csl_rr_free, af_csl_rr_free, ef_csl_rr_free,
  x_csl_rr_free_invalid, u_csl_rr_free_invalid, an_csl_rr_free_invalid, en_csl_rr_free_invalid,
  au_csl_rr_free_invalid, eu_csl_rr_free_invalid, ag_csl_rr_free_invalid, eg_csl_rr_free_invalid,
  ax_csl_rr_free_invalid, ex_csl_rr_free_invalid, af_csl_rr_free_invalid, ef_csl_rr_free_invalid,
  x_csl_rr_cas, u_csl_rr_cas, an_csl_rr_cas, en_csl_rr_cas, au_csl_rr_cas, eu_csl_rr_cas,
  ag_csl_rr_cas, eg_csl_rr_cas, ax_csl_rr_cas, ex_csl_rr_cas, af_csl_rr_cas, ef_csl_rr_cas,
  x_csl_rr_cas_value, u_csl_rr_cas_value, an_csl_rr_cas_value, en_csl_rr_cas_value,
  au_csl_rr_cas_value, eu_csl_rr_cas_value, ag_csl_rr_cas_value, eg_csl_rr_cas_value,
  ax_csl_rr_cas_value, ex_csl_rr_cas_value, af_csl_rr_cas_value, ef_csl_rr_cas_value,
  x_csl_rr_cas_missing, u_csl_rr_cas_missing, an_csl_rr_cas_missing, en_csl_rr_cas_missing,
  au_csl_rr_cas_missing, eu_csl_rr_cas_missing, ag_csl_rr_cas_missing, eg_csl_rr_cas_missing,
  ax_csl_rr_cas_missing, ex_csl_rr_cas_missing, af_csl_rr_cas_missing, ef_csl_rr_cas_missing,
  x_csl_rr_eval, u_csl_rr_eval, an_csl_rr_eval, en_csl_rr_eval, au_csl_rr_eval, eu_csl_rr_eval,
  ag_csl_rr_eval, eg_csl_rr_eval, ax_csl_rr_eval, ex_csl_rr_eval, af_csl_rr_eval, ef_csl_rr_eval,
  x_csl_rr_assign, u_csl_rr_assign, an_csl_rr_assign, en_csl_rr_assign, au_csl_rr_assign,
  eu_csl_rr_assign, ag_csl_rr_assign, eg_csl_rr_assign, ax_csl_rr_assign, ex_csl_rr_assign,
  af_csl_rr_assign, ef_csl_rr_assign, x_csl_rr_if, u_csl_rr_if, an_csl_rr_if, en_csl_rr_if,
  au_csl_rr_if, eu_csl_rr_if, ag_csl_rr_if, eg_csl_rr_if, ax_csl_rr_if, ex_csl_rr_if, af_csl_rr_if,
  ef_csl_rr_if, x_csl_rr_until_none_unfold, u_csl_rr_until_none_unfold,
  an_csl_rr_until_none_unfold, en_csl_rr_until_none_unfold, au_csl_rr_until_none_unfold,
  eu_csl_rr_until_none_unfold, ag_csl_rr_until_none_unfold, eg_csl_rr_until_none_unfold,
  ax_csl_rr_until_none_unfold, ex_csl_rr_until_none_unfold, af_csl_rr_until_none_unfold,
  ef_csl_rr_until_none_unfold, x_csl_rr_while_unfold, u_csl_rr_while_unfold,
  an_csl_rr_while_unfold, en_csl_rr_while_unfold, au_csl_rr_while_unfold, eu_csl_rr_while_unfold,
  ag_csl_rr_while_unfold, eg_csl_rr_while_unfold, ax_csl_rr_while_unfold, ex_csl_rr_while_unfold,
  af_csl_rr_while_unfold, ef_csl_rr_while_unfold, x_csl_rr_exp_lit, u_csl_rr_exp_lit,
  an_csl_rr_exp_lit, en_csl_rr_exp_lit, au_csl_rr_exp_lit, eu_csl_rr_exp_lit, ag_csl_rr_exp_lit,
  eg_csl_rr_exp_lit, ax_csl_rr_exp_lit, ex_csl_rr_exp_lit, af_csl_rr_exp_lit, ef_csl_rr_exp_lit,
  an_csl_rr_exp_var, en_csl_rr_exp_var, au_csl_rr_exp_var, eu_csl_rr_exp_var, ax_csl_rr_exp_var,
  ex_csl_rr_exp_var, af_csl_rr_exp_var, ef_csl_rr_exp_var, x_csl_rr_exp_var_missing,
  u_csl_rr_exp_var_missing, an_csl_rr_exp_var_missing, en_csl_rr_exp_var_missing,
  au_csl_rr_exp_var_missing, eu_csl_rr_exp_var_missing, ag_csl_rr_exp_var_missing,
  eg_csl_rr_exp_var_missing, ax_csl_rr_exp_var_missing, ex_csl_rr_exp_var_missing,
  af_csl_rr_exp_var_missing, ef_csl_rr_exp_var_missing, x_csl_rr_exp_plus, u_csl_rr_exp_plus,
  an_csl_rr_exp_plus, en_csl_rr_exp_plus, au_csl_rr_exp_plus, eu_csl_rr_exp_plus,
  ag_csl_rr_exp_plus, eg_csl_rr_exp_plus, ax_csl_rr_exp_plus, ex_csl_rr_exp_plus,
  af_csl_rr_exp_plus, ef_csl_rr_exp_plus, x_csl_rr_exp_minus, u_csl_rr_exp_minus,
  an_csl_rr_exp_minus, en_csl_rr_exp_minus, au_csl_rr_exp_minus, eu_csl_rr_exp_minus,
  ag_csl_rr_exp_minus, eg_csl_rr_exp_minus, ax_csl_rr_exp_minus, ex_csl_rr_exp_minus,
  af_csl_rr_exp_minus, ef_csl_rr_exp_minus, x_csl_rr_exp_mult, u_csl_rr_exp_mult,
  an_csl_rr_exp_mult, en_csl_rr_exp_mult, au_csl_rr_exp_mult, eu_csl_rr_exp_mult,
  ag_csl_rr_exp_mult, eg_csl_rr_exp_mult, ax_csl_rr_exp_mult, ex_csl_rr_exp_mult,
  af_csl_rr_exp_mult, ef_csl_rr_exp_mult, x_csl_rr_guard.
-/
