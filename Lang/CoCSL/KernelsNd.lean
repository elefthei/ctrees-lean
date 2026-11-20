/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Early

/-!
# CoCSL nondeterministic temporal kernels

For every focused source instruction under the nondeterministic runner: the q-polymorphic
next-step (`x_csl_nd_*`) and until (`u_csl_nd_*`) rules over `SbProper` predicates, the `AG`/`EG`
rules, and the formula-level corollaries used downstream (← `Lang/CoCSL/Mod.v`, lines 3626-7672).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield
open ITree (Effect)

local notation "WN" => writerE (CSLObs (Nat × Nat))
local notation "TN" => ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)

/-! ## Congruence helpers -/

section Helpers
variable {q : Ticlq} {P Q : TN → World WN → Prop} {w : World WN}

private theorem qnext_brSn_iff {n : Nat} (hlive : ∀ t w, P t w → NotDone w)
    {k : Fin (n + 1) → TN} :
    qnext q P Q (CTree.brSn (n + 1) k) w ↔
      P (CTree.brSn (n + 1) k) w ∧
        match q with
        | .A => ∀ j, Q (k j) w
        | .E => ∃ j, Q (k j) w := by
  refine (qnext_brS_iff (B := Bn) (c := ⟨n + 1⟩) ⟨0⟩ hlive).trans ?_
  cases q
  · exact and_congr_right' ⟨fun h j => h ⟨j⟩, fun h j => h j.down⟩
  · exact and_congr_right' ⟨fun ⟨j, h⟩ => ⟨j.down, h⟩, fun ⟨j, h⟩ => ⟨⟨j⟩, h⟩⟩

private theorem quntil_brSn_iff {n : Nat} (hlive : ∀ t w, P t w → NotDone w)
    {k : Fin (n + 1) → TN} :
    quntil q P Q (CTree.brSn (n + 1) k) w ↔
      Q (CTree.brSn (n + 1) k) w ∨
        (P (CTree.brSn (n + 1) k) w ∧
          match q with
          | .A => ∀ j, quntil q P Q (k j) w
          | .E => ∃ j, quntil q P Q (k j) w) :=
  quntil_unfold.trans (or_congr_right (qnext_brSn_iff hlive))

private theorem stuck_dead : ∀ (u : TN) z, ¬ ktrans (.stuck : TN) w u z :=
  fun _ _ => ktrans_stuck

private theorem ag_dead {φ : TiclL WN} {t : TN}
    (h : ∀ u z, ¬ ktrans t w u z) : ¬ entails (.cg .A φ) t w :=
  fun H => let ⟨_, ⟨u, z, tr⟩, _⟩ := agc_unfold.1 H; h u z tr

private theorem eg_dead {φ : TiclL WN} {t : TN}
    (h : ∀ u z, ¬ ktrans t w u z) : ¬ entails (.cg .E φ) t w :=
  fun H => let ⟨_, u, z, tr, _⟩ := egc_unfold.1 H; h u z tr

end Helpers

/-! ## Complete scheduled command and expression modalities

Hypotheses of every `x`/`u` kernel: `(q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
(hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q)`. -/

/-! ### read -/

theorem x_csl_nd_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some value →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some value))) (some i)
        ((h, allocs), (ctx, c))) w) :=
  fun h0 => qnext_sb hP hQ (interp_nd_source_read_value n ts i a value K h allocs ctx c h0)

theorem u_csl_nd_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some value →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some value))) (some i)
        ((h, allocs), (ctx, c))) w) :=
  fun h0 => quntil_sb hP hQ (interp_nd_source_read_value n ts i a value K h allocs ctx c h0)

theorem ag_csl_nd_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a = some value →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some value))) (some i)
        ((h, allocs), (ctx, c))) w) :=
  fun h0 => proper_entails_meq _ (interp_nd_source_read_value n ts i a value K h allocs ctx c h0)

theorem eg_csl_nd_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a = some value →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some value))) (some i)
        ((h, allocs), (ctx, c))) w) :=
  fun h0 => proper_entails_meq _ (interp_nd_source_read_value n ts i a value K h allocs ctx c h0)

/-! ### read_missing -/

theorem x_csl_nd_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 => (qnext_sb hP hQ (interp_nd_source_read_missing n ts i a K h allocs ctx c h0)).trans
    (qnext_dead_iff stuck_dead)

theorem u_csl_nd_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ Q (.stuck : TN) w) :=
  fun h0 => (quntil_sb hP hQ (interp_nd_source_read_missing n ts i a K h allocs ctx c h0)).trans
    (quntil_dead_iff stuck_dead)

theorem ag_csl_nd_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a = none →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => ag_dead stuck_dead
    ((proper_entails_meq _ (interp_nd_source_read_missing n ts i a K h allocs ctx c h0)).1 H)

theorem eg_csl_nd_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a = none →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.read a) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => eg_dead stuck_dead
    ((proper_entails_meq _ (interp_nd_source_read_missing n ts i a K h allocs ctx c h0)).1 H)

/-! ### write -/

theorem x_csl_nd_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a ≠ none →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      P (log (CSLObs.heap (upd h a value, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            ((upd h a value, allocs), (ctx, c))) w ∧
        Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            ((upd h a value, allocs), (ctx, c)))
          (.obs (E := WN) (CSLObs.heap (upd h a value, allocs)) ⟨⟩)) :=
  fun h0 =>
    (qnext_sb hP hQ (interp_nd_source_write_present n ts i a value K h allocs ctx c h0)).trans
    (qnext_log_iff hlive)

theorem u_csl_nd_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a ≠ none →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      Q (log (CSLObs.heap (upd h a value, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            ((upd h a value, allocs), (ctx, c))) w ∨
        (P (log (CSLObs.heap (upd h a value, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              ((upd h a value, allocs), (ctx, c))) w ∧
          quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              ((upd h a value, allocs), (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (upd h a value, allocs)) ⟨⟩))) :=
  fun h0 =>
    (quntil_sb hP hQ (interp_nd_source_write_present n ts i a value K h allocs ctx c h0)).trans
      (quntil_log_iff hlive)

theorem ag_csl_nd_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a ≠ none →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.write a value) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      entails φ (log (CSLObs.heap (upd h a value, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            ((upd h a value, allocs), (ctx, c))) w ∧
        entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            ((upd h a value, allocs), (ctx, c)))
          (.obs (E := WN) (CSLObs.heap (upd h a value, allocs)) ⟨⟩)) :=
  fun h0 => (proper_entails_meq _
    (interp_nd_source_write_present n ts i a value K h allocs ctx c h0)).trans ag_log_iff

theorem eg_csl_nd_write (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a ≠ none →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.write a value) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      entails φ (log (CSLObs.heap (upd h a value, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            ((upd h a value, allocs), (ctx, c))) w ∧
        entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            ((upd h a value, allocs), (ctx, c)))
          (.obs (E := WN) (CSLObs.heap (upd h a value, allocs)) ⟨⟩)) :=
  fun h0 => (proper_entails_meq _
    (interp_nd_source_write_present n ts i a value K h allocs ctx c h0)).trans eg_log_iff

/-! ### write_missing -/

theorem x_csl_nd_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 => (qnext_sb hP hQ
    (interp_nd_source_write_missing n ts i a value K h allocs ctx c h0)).trans
    (qnext_dead_iff stuck_dead)

theorem u_csl_nd_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.write a value) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ Q (.stuck : TN) w) :=
  fun h0 => (quntil_sb hP hQ
    (interp_nd_source_write_missing n ts i a value K h allocs ctx c h0)).trans
    (quntil_dead_iff stuck_dead)

theorem ag_csl_nd_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a = none →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.write a value) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      False) :=
  fun h0 => iff_false_intro fun H => ag_dead stuck_dead ((proper_entails_meq _
    (interp_nd_source_write_missing n ts i a value K h allocs ctx c h0)).1 H)

theorem eg_csl_nd_write_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a value : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    h a = none →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.write a value) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      False) :=
  fun h0 => iff_false_intro fun H => eg_dead stuck_dead ((proper_entails_meq _
    (interp_nd_source_write_missing n ts i a value K h allocs ctx c h0)).1 H)

/-! ### emit (the `AG` rule `ag_csl_nd_emit` lives in `Lang.CoCSL.Early`) -/

theorem x_csl_nd_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      P (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            (memory, (ctx, c + 1))) w ∧
        Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            (memory, (ctx, c + 1)))
          (.obs (E := WN) (CSLObs.emit (stamp (tag, value) c)) ⟨⟩) :=
  (qnext_sb hP hQ (interp_nd_source_emit_log n ts i tag value K memory ctx c)).trans
    (qnext_log_iff hlive)

theorem u_csl_nd_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.emit tag value) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      Q (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            (memory, (ctx, c + 1))) w ∨
        (P (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory, (ctx, c + 1))) w ∧
          quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory, (ctx, c + 1)))
            (.obs (E := WN) (CSLObs.emit (stamp (tag, value) c)) ⟨⟩)) :=
  (quntil_sb hP hQ (interp_nd_source_emit_log n ts i tag value K memory ctx c)).trans
    (quntil_log_iff hlive)

theorem eg_csl_nd_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails φ (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            (memory, (ctx, c + 1))) w ∧
        entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            (memory, (ctx, c + 1)))
          (.obs (E := WN) (CSLObs.emit (stamp (tag, value) c)) ⟨⟩) :=
  (proper_entails_meq _ (interp_nd_source_emit_log n ts i tag value K memory ctx c)).trans
    eg_log_iff

/-! ### yield (the `AG` rule `ag_csl_nd_yield` lives in `Lang.CoCSL.Early`) -/

private theorem nd_yield_select (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (σ : SSig) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow .yield >>= K)) (some i) σ ~
      CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some j) σ :=
  sbisim_trans (interp_nd_source_yield n ts i K σ) (interp_schedule_nd_select sh n _ σ)

theorem x_csl_nd_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow .yield >>= K))
        (some i) (memory, (ctx, c))) w ↔
      P (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
          (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∧
        match q with
        | .A => ∀ j : Fin (n + 1), Q (interp_schedule_nd sh (n + 1)
            (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w
        | .E => ∃ j : Fin (n + 1), Q (interp_schedule_nd sh (n + 1)
            (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w :=
  (qnext_sb hP hQ (nd_yield_select n ts i K _)).trans (qnext_brSn_iff hlive)

theorem u_csl_nd_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow .yield >>= K))
        (some i) (memory, (ctx, c))) w ↔
      Q (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
          (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∨
        (P (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
            (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∧
          match q with
          | .A => ∀ j : Fin (n + 1), quntil q P Q (interp_schedule_nd sh (n + 1)
              (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w
          | .E => ∃ j : Fin (n + 1), quntil q P Q (interp_schedule_nd sh (n + 1)
              (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w) :=
  (quntil_sb hP hQ (nd_yield_select n ts i K _)).trans (quntil_brSn_iff hlive)

theorem eg_csl_nd_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow .yield >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
          (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w ∧
        ∃ j : Fin (n + 1), entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
          (ts.set i (K (some ()))) (some j) (memory, (ctx, c))) w :=
  (proper_entails_meq _ (interp_nd_source_yield n ts i K _)).trans
    (eg_csl_nd_select n memory ctx c _ w φ)

/-! ### fork -/

theorem x_csl_nd_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (child : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.fork child) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 2)
        (Vector.cons (denote_flow child >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) (memory, (ctx, c))) w :=
  qnext_sb hP hQ (interp_nd_source_fork n ts i child K _)

theorem u_csl_nd_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (child : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.fork child) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 2)
        (Vector.cons (denote_flow child >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) (memory, (ctx, c))) w :=
  quntil_sb hP hQ (interp_nd_source_fork n ts i child K _)

theorem ag_csl_nd_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (child : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.fork child) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 2)
        (Vector.cons (denote_flow child >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) (memory, (ctx, c))) w :=
  proper_entails_meq _ (interp_nd_source_fork n ts i child K _)

theorem eg_csl_nd_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (child : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.fork child) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 2)
        (Vector.cons (denote_flow child >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) (memory, (ctx, c))) w :=
  proper_entails_meq _ (interp_nd_source_fork n ts i child K _)

/-! ### ret -/

theorem x_csl_nd_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (x : A) (K : Option A → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some x))) (some i)
        (memory, (ctx, c))) w := by
  rw [interp_nd_source_ret]

theorem u_csl_nd_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (x : A) (K : Option A → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some x))) (some i)
        (memory, (ctx, c))) w := by
  rw [interp_nd_source_ret]

theorem ag_csl_nd_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (x : A) (K : Option A → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some x))) (some i)
        (memory, (ctx, c))) w := by
  rw [interp_nd_source_ret]

theorem eg_csl_nd_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (x : A) (K : Option A → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some x))) (some i)
        (memory, (ctx, c))) w := by
  rw [interp_nd_source_ret]

/-! ### bind -/

theorem x_csl_nd_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.bind p next) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow p >>= fun flow =>
          match flow with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_bind]; exact Iff.rfl

theorem u_csl_nd_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.bind p next) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow p >>= fun flow =>
          match flow with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_bind]; exact Iff.rfl

theorem ag_csl_nd_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.bind p next) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow p >>= fun flow =>
          match flow with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_bind]; exact Iff.rfl

theorem eg_csl_nd_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.bind p next) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow p >>= fun flow =>
          match flow with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_bind]; exact Iff.rfl

/-! ### alloc_first -/

theorem x_csl_nd_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      P (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
        Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c)))
          (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩)) :=
  fun h0 h1 h2 h3 => (qnext_sb hP hQ (interp_nd_source_alloc_first n ts i size base K h allocs
    ctx c h0 h1 h2 h3)).trans (qnext_log_iff hlive)

theorem u_csl_nd_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      Q (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c))) w ∨
        (P (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat)) >>=
            fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
              (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
          quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
              (managed_alloc (h, allocs) base size, (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩))) :=
  fun h0 h1 h2 h3 => (quntil_sb hP hQ (interp_nd_source_alloc_first n ts i size base K h allocs
    ctx c h0 h1 h2 h3)).trans (quntil_log_iff hlive)

theorem ag_csl_nd_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.alloc size) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      entails φ (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat))
          >>= fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
        entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c)))
          (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩)) :=
  fun h0 h1 h2 h3 => (proper_entails_meq _ (interp_nd_source_alloc_first n ts i size base K h
    allocs ctx c h0 h1 h2 h3)).trans ag_log_iff

theorem eg_csl_nd_alloc_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size base : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    0 < size → 0 < base → block_free h base size →
    (∀ j, 0 < j → j < base → ¬ block_free h j size) →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.alloc size) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      entails φ (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat))
          >>= fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
        entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            (managed_alloc (h, allocs) base size, (ctx, c)))
          (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩)) :=
  fun h0 h1 h2 h3 => (proper_entails_meq _ (interp_nd_source_alloc_first n ts i size base K h
    allocs ctx c h0 h1 h2 h3)).trans eg_log_iff

/-! ### alloc: first-fit over a finite heap -/

theorem x_csl_nd_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    heap_finite h → 0 < size →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      ∀ base, 0 < base → block_free h base size →
        (∀ j, 0 < j → j < base → ¬ block_free h j size) →
        (P (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat)) >>=
            fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
              (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
          Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
              (managed_alloc (h, allocs) base size, (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfi =>
    x_csl_nd_alloc_first n ts i size base K h allocs ctx c w q P Q hP hlive hQ hpos hb hf hfi

theorem u_csl_nd_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    heap_finite h → 0 < size →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔
      ∀ base, 0 < base → block_free h base size →
        (∀ j, 0 < j → j < base → ¬ block_free h j size) →
        (Q (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat)) >>=
            fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
              (managed_alloc (h, allocs) base size, (ctx, c))) w ∨
          (P (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat)) >>=
              fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
                (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
            quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
                (managed_alloc (h, allocs) base size, (ctx, c)))
              (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩)))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfi =>
    u_csl_nd_alloc_first n ts i size base K h allocs ctx c w q P Q hP hlive hQ hpos hb hf hfi

theorem ag_csl_nd_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    heap_finite h → 0 < size →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.alloc size) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      ∀ base, 0 < base → block_free h base size →
        (∀ j, 0 < j → j < base → ¬ block_free h j size) →
        (entails φ (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat))
            >>= fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
              (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
          entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some base)))
              (some i) (managed_alloc (h, allocs) base size, (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfi =>
    ag_csl_nd_alloc_first n ts i size base K h allocs ctx c w φ hpos hb hf hfi

theorem eg_csl_nd_alloc (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    heap_finite h → 0 < size →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.alloc size) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      ∀ base, 0 < base → block_free h base size →
        (∀ j, 0 < j → j < base → ¬ block_free h j size) →
        (entails φ (log (CSLObs.heap (managed_alloc (h, allocs) base size) : CSLObs (Nat × Nat))
            >>= fun _ => interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
              (managed_alloc (h, allocs) base size, (ctx, c))) w ∧
          entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some base)))
              (some i) (managed_alloc (h, allocs) base size, (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (managed_alloc (h, allocs) base size)) ⟨⟩))) :=
  fun hfin hpos => first_fit_iff hfin hpos fun base hb hf hfi =>
    eg_csl_nd_alloc_first n ts i size base K h allocs ctx c w φ hpos hb hf hfi

/-! ### alloc_zero -/

theorem x_csl_nd_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False :=
  (qnext_sb hP hQ (interp_nd_source_alloc_zero n ts i K h allocs ctx c)).trans
    (qnext_dead_iff stuck_dead)

theorem u_csl_nd_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ Q (.stuck : TN) w :=
  (quntil_sb hP hQ (interp_nd_source_alloc_zero n ts i K h allocs ctx c)).trans
    (quntil_dead_iff stuck_dead)

theorem ag_csl_nd_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False :=
  iff_false_intro fun H => ag_dead stuck_dead
    ((proper_entails_meq _ (interp_nd_source_alloc_zero n ts i K h allocs ctx c)).1 H)

theorem eg_csl_nd_alloc_zero (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc 0) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False :=
  iff_false_intro fun H => eg_dead stuck_dead
    ((proper_entails_meq _ (interp_nd_source_alloc_zero n ts i K h allocs ctx c)).1 H)

/-! ### alloc_no_space -/

theorem x_csl_nd_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 h1 => (qnext_sb hP hQ
    (interp_nd_source_alloc_no_space n ts i size K h allocs ctx c h0 h1)).trans
    (qnext_dead_iff spin_no_ktrans)

theorem u_csl_nd_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.alloc size) >>= K))
        (some i) ((h, allocs), (ctx, c))) w ↔ Q (CTree.spin : TN) w) :=
  fun h0 h1 => (quntil_sb hP hQ
    (interp_nd_source_alloc_no_space n ts i size K h allocs ctx c h0 h1)).trans
    (quntil_dead_iff spin_no_ktrans)

theorem ag_csl_nd_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.alloc size) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      False) :=
  fun h0 h1 => iff_false_intro fun H => ag_dead spin_no_ktrans ((proper_entails_meq _
    (interp_nd_source_alloc_no_space n ts i size K h allocs ctx c h0 h1)).1 H)

theorem eg_csl_nd_alloc_no_space (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (size : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    0 < size → (∀ base, 0 < base → ¬ block_free h base size) →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.alloc size) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      False) :=
  fun h0 h1 => iff_false_intro fun H => eg_dead spin_no_ktrans ((proper_entails_meq _
    (interp_nd_source_alloc_no_space n ts i size K h allocs ctx c h0 h1)).1 H)

/-! ### free -/

theorem x_csl_nd_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory memory' : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = some memory' →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.free base) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      match base with
      | 0 => qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory', (ctx, c))) w
      | _ + 1 => P (log (CSLObs.heap memory' : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory', (ctx, c))) w ∧
          Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory', (ctx, c))) (.obs (E := WN) (CSLObs.heap memory') ⟨⟩)) := by
  intro h0
  refine (qnext_sb hP hQ (interp_nd_source_free n ts i base K memory memory' ctx c h0)).trans ?_
  cases base
  · exact Iff.rfl
  · exact qnext_log_iff hlive

theorem u_csl_nd_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory memory' : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = some memory' →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.free base) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      match base with
      | 0 => quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          (memory', (ctx, c))) w
      | _ + 1 => Q (log (CSLObs.heap memory' : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory', (ctx, c))) w ∨
          (P (log (CSLObs.heap memory' : CSLObs (Nat × Nat)) >>= fun _ =>
              interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
                (memory', (ctx, c))) w ∧
            quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
                (memory', (ctx, c))) (.obs (E := WN) (CSLObs.heap memory') ⟨⟩))) := by
  intro h0
  refine (quntil_sb hP hQ (interp_nd_source_free n ts i base K memory memory' ctx c h0)).trans ?_
  cases base
  · exact Iff.rfl
  · exact quntil_log_iff hlive

theorem ag_csl_nd_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory memory' : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    managed_free memory base = some memory' →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.free base) >>= K)) (some i) (memory, (ctx, c))) w ↔
      match base with
      | 0 => entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ())))
          (some i) (memory', (ctx, c))) w
      | _ + 1 => entails φ (log (CSLObs.heap memory' : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory', (ctx, c))) w ∧
          entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory', (ctx, c))) (.obs (E := WN) (CSLObs.heap memory') ⟨⟩)) := by
  intro h0
  refine (proper_entails_meq _
    (interp_nd_source_free n ts i base K memory memory' ctx c h0)).trans ?_
  cases base
  · exact Iff.rfl
  · exact ag_log_iff

theorem eg_csl_nd_free (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory memory' : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    managed_free memory base = some memory' →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.free base) >>= K)) (some i) (memory, (ctx, c))) w ↔
      match base with
      | 0 => entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ())))
          (some i) (memory', (ctx, c))) w
      | _ + 1 => entails φ (log (CSLObs.heap memory' : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory', (ctx, c))) w ∧
          entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory', (ctx, c))) (.obs (E := WN) (CSLObs.heap memory') ⟨⟩)) := by
  intro h0
  refine (proper_entails_meq _
    (interp_nd_source_free n ts i base K memory memory' ctx c h0)).trans ?_
  cases base
  · exact Iff.rfl
  · exact eg_log_iff

/-! ### free_invalid -/

theorem x_csl_nd_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = none →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.free base) >>= K))
        (some i) (memory, (ctx, c))) w ↔ False) :=
  fun h0 => (qnext_sb hP hQ
    (interp_nd_source_free_invalid n ts i base K memory ctx c h0)).trans
    (qnext_dead_iff stuck_dead)

theorem u_csl_nd_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    managed_free memory base = none →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.free base) >>= K))
        (some i) (memory, (ctx, c))) w ↔ Q (.stuck : TN) w) :=
  fun h0 => (quntil_sb hP hQ
    (interp_nd_source_free_invalid n ts i base K memory ctx c h0)).trans
    (quntil_dead_iff stuck_dead)

theorem ag_csl_nd_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    managed_free memory base = none →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.free base) >>= K)) (some i) (memory, (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => ag_dead stuck_dead ((proper_entails_meq _
    (interp_nd_source_free_invalid n ts i base K memory ctx c h0)).1 H)

theorem eg_csl_nd_free_invalid (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    managed_free memory base = none →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.free base) >>= K)) (some i) (memory, (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => eg_dead stuck_dead ((proper_entails_meq _
    (interp_nd_source_free_invalid n ts i base K memory ctx c h0)).1 H)

/-! ### cas (expression operands) -/

theorem x_csl_nd_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp a >>= fun addr => denote_exp expected >>= fun old =>
          denote_exp desired >>= fun value =>
            denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_cas_exp]

theorem u_csl_nd_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp a >>= fun addr => denote_exp expected >>= fun old =>
          denote_exp desired >>= fun value =>
            denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_cas_exp]

theorem ag_csl_nd_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp a >>= fun addr => denote_exp expected >>= fun old =>
          denote_exp desired >>= fun value =>
            denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_cas_exp]

theorem eg_csl_nd_cas (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : CExp) (K : Option Bool → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas a expected desired) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp a >>= fun addr => denote_exp expected >>= fun old =>
          denote_exp desired >>= fun value =>
            denote_flow (.cas (.lit addr) (.lit old) (.lit value)) >>= K))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_cas_exp]

/-! ### cas_value -/

theorem x_csl_nd_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (hP : SbProper P) (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some current →
    (qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔
      if current = expected then
        P (log (CSLObs.heap (upd h a desired, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
              ((upd h a desired, allocs), (ctx, c))) w ∧
          Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
              ((upd h a desired, allocs), (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (upd h a desired, allocs)) ⟨⟩)
      else
        qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some false))) (some i)
          ((h, allocs), (ctx, c))) w) := by
  intro h0
  refine (qnext_sb hP hQ (interp_nd_source_cas_value n ts i a expected desired current K h allocs
    ctx c h0)).trans ?_
  by_cases hc : current = expected
  · simp only [hc, ↓reduceIte]; exact qnext_log_iff hlive
  · simp only [hc, ↓reduceIte]

theorem u_csl_nd_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (hP : SbProper P) (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = some current →
    (quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔
      if current = expected then
        Q (log (CSLObs.heap (upd h a desired, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
              ((upd h a desired, allocs), (ctx, c))) w ∨
          (P (log (CSLObs.heap (upd h a desired, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
              interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
                ((upd h a desired, allocs), (ctx, c))) w ∧
            quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
                ((upd h a desired, allocs), (ctx, c)))
              (.obs (E := WN) (CSLObs.heap (upd h a desired, allocs)) ⟨⟩))
      else
        quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K (some false))) (some i)
          ((h, allocs), (ctx, c))) w) := by
  intro h0
  refine (quntil_sb hP hQ (interp_nd_source_cas_value n ts i a expected desired current K h
    allocs ctx c h0)).trans ?_
  by_cases hc : current = expected
  · simp only [hc, ↓reduceIte]; exact quntil_log_iff hlive
  · simp only [hc, ↓reduceIte]

theorem ag_csl_nd_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    h a = some current →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔
      if current = expected then
        entails φ (log (CSLObs.heap (upd h a desired, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
              ((upd h a desired, allocs), (ctx, c))) w ∧
          entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
              ((upd h a desired, allocs), (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (upd h a desired, allocs)) ⟨⟩)
      else
        entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some false))) (some i)
          ((h, allocs), (ctx, c))) w) := by
  intro h0
  refine (proper_entails_meq _ (interp_nd_source_cas_value n ts i a expected desired current K h
    allocs ctx c h0)).trans ?_
  by_cases hc : current = expected
  · simp only [hc, ↓reduceIte]; exact ag_log_iff
  · simp only [hc, ↓reduceIte]

theorem eg_csl_nd_cas_value (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired current : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    h a = some current →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔
      if current = expected then
        entails φ (log (CSLObs.heap (upd h a desired, allocs) : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
              ((upd h a desired, allocs), (ctx, c))) w ∧
          entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some true))) (some i)
              ((upd h a desired, allocs), (ctx, c)))
            (.obs (E := WN) (CSLObs.heap (upd h a desired, allocs)) ⟨⟩)
      else
        entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some false))) (some i)
          ((h, allocs), (ctx, c))) w) := by
  intro h0
  refine (proper_entails_meq _ (interp_nd_source_cas_value n ts i a expected desired current K h
    allocs ctx c h0)).trans ?_
  by_cases hc : current = expected
  · simp only [hc, ↓reduceIte]; exact eg_log_iff
  · simp only [hc, ↓reduceIte]

/-! ### cas_missing -/

theorem x_csl_nd_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none →
    (qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 => (qnext_sb hP hQ (interp_nd_source_cas_missing n ts i a expected desired K h allocs
    ctx c h0)).trans (qnext_dead_iff stuck_dead)

theorem u_csl_nd_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    h a = none →
    (quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔ Q (.stuck : TN) w) :=
  fun h0 => (quntil_sb hP hQ (interp_nd_source_cas_missing n ts i a expected desired K h allocs
    ctx c h0)).trans (quntil_dead_iff stuck_dead)

theorem ag_csl_nd_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    h a = none →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => ag_dead stuck_dead ((proper_entails_meq _
    (interp_nd_source_cas_missing n ts i a expected desired K h allocs ctx c h0)).1 H)

theorem eg_csl_nd_cas_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a expected desired : Nat) (K : Option Bool → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    h a = none →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.cas (.lit a) (.lit expected) (.lit desired)) >>= K)) (some i)
        ((h, allocs), (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => eg_dead stuck_dead ((proper_entails_meq _
    (interp_nd_source_cas_missing n ts i a expected desired K h allocs ctx c h0)).1 H)

/-! ### eval -/

theorem x_csl_nd_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (e : CExp) (K : Option Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.eval e) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => K (some value))) (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_eval]

theorem u_csl_nd_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (e : CExp) (K : Option Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.eval e) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => K (some value))) (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_eval]

theorem ag_csl_nd_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (e : CExp) (K : Option Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.eval e) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => K (some value))) (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_eval]

theorem eg_csl_nd_eval (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (e : CExp) (K : Option Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.eval e) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => K (some value))) (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_eval]

/-! ### assign -/

theorem x_csl_nd_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (e : CExp) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.assign name e) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => source_get >>= fun ctx =>
          source_put (Ctx.add name value ctx) >>= fun _ => K (some ())))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_assign]

theorem u_csl_nd_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (e : CExp) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.assign name e) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => source_get >>= fun ctx =>
          source_put (Ctx.add name value ctx) >>= fun _ => K (some ())))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_assign]

theorem ag_csl_nd_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (e : CExp) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.assign name e) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => source_get >>= fun ctx =>
          source_put (Ctx.add name value ctx) >>= fun _ => K (some ())))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_assign]

theorem eg_csl_nd_assign (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (e : CExp) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.assign name e) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp e >>= fun value => source_get >>= fun ctx =>
          source_put (Ctx.add name value ctx) >>= fun _ => K (some ())))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_assign]

/-! ### if -/

theorem x_csl_nd_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then denote_flow yes >>= K else denote_flow no >>= K))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_if]

theorem u_csl_nd_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ite test yes no) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then denote_flow yes >>= K else denote_flow no >>= K))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_if]

theorem ag_csl_nd_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then denote_flow yes >>= K else denote_flow no >>= K))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_if]

theorem eg_csl_nd_if {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (yes no : CProg A) (K : Option A → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.ite test yes no) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then denote_flow yes >>= K else denote_flow no >>= K))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_if]

/-! ### until_none_unfold -/

theorem x_csl_nd_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq)
    (P Q : TN → World WN → Prop) (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow body >>= until_tail body K))
        (some i) (memory, (ctx, c))) w :=
  by rw [source_raw_until]

theorem u_csl_nd_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq)
    (P Q : TN → World WN → Prop) (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w)
    (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.untilNone body) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow body >>= until_tail body K)) (some i) (memory, (ctx, c))) w :=
  by rw [source_raw_until]

theorem ag_csl_nd_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow body >>= until_tail body K)) (some i) (memory, (ctx, c))) w :=
  by rw [source_raw_until]

theorem eg_csl_nd_until_none_unfold {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (memory : ManagedHeap) (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow body >>= until_tail body K)) (some i) (memory, (ctx, c))) w :=
  by rw [source_raw_until]

/-! ### while_unfold -/

theorem x_csl_nd_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.while test body) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then
            denote_flow body >>= fun flow =>
              match flow with
              | none => K none
              | some _ => .guard (denote_flow (.while test body) >>= K)
          else K (some ())))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_while_unfold]; exact Iff.rfl

theorem u_csl_nd_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop)
    (_hP : SbProper P) (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.while test body) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then
            denote_flow body >>= fun flow =>
              match flow with
              | none => K none
              | some _ => .guard (denote_flow (.while test body) >>= K)
          else K (some ())))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_while_unfold]; exact Iff.rfl

theorem ag_csl_nd_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.while test body) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then
            denote_flow body >>= fun flow =>
              match flow with
              | none => K none
              | some _ => .guard (denote_flow (.while test body) >>= K)
          else K (some ())))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_while_unfold]; exact Iff.rfl

theorem eg_csl_nd_while_unfold (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.while test body) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp test >>= fun value =>
          if is_true value then
            denote_flow body >>= fun flow =>
              match flow with
              | none => K none
              | some _ => .guard (denote_flow (.while test body) >>= K)
          else K (some ())))
        (some i) (memory, (ctx, c))) w := by
  rw [interp_nd_source_while_unfold]; exact Iff.rfl

/-! ### exp_lit -/

theorem x_csl_nd_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.lit value) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K value)) (some i)
        (memory, (ctx, c))) w :=
  by rw [interp_nd_lit]

theorem u_csl_nd_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.lit value) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (K value)) (some i)
        (memory, (ctx, c))) w :=
  by rw [interp_nd_lit]

theorem ag_csl_nd_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.lit value) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (K value)) (some i)
        (memory, (ctx, c))) w :=
  by rw [interp_nd_lit]

theorem eg_csl_nd_exp_lit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.lit value) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (K value)) (some i)
        (memory, (ctx, c))) w :=
  by rw [interp_nd_lit]

/-! ### exp_var: a present variable yields once (a scheduling point) -/

private theorem nd_var_select (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (h0 : Ctx.lookup name ctx = some value) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K)) (some i)
        (memory, (ctx, c)) ~
      CTree.brSn (n + 1) fun j =>
        interp_schedule_nd sh (n + 1) (ts.set i (K value)) (some j) (memory, (ctx, c)) :=
  sbisim_trans (interp_nd_var n ts i name value K _ h0) (interp_schedule_nd_select sh n _ _)

theorem x_csl_nd_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = some value →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      P (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
          (ts.set i (K value)) (some j) (memory, (ctx, c))) w ∧
        match q with
        | .A => ∀ j : Fin (n + 1), Q (interp_schedule_nd sh (n + 1)
            (ts.set i (K value)) (some j) (memory, (ctx, c))) w
        | .E => ∃ j : Fin (n + 1), Q (interp_schedule_nd sh (n + 1)
            (ts.set i (K value)) (some j) (memory, (ctx, c))) w) :=
  fun h0 => (qnext_sb hP hQ (nd_var_select n ts i name value K memory ctx c h0)).trans
    (qnext_brSn_iff hlive)

theorem u_csl_nd_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = some value →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      Q (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
          (ts.set i (K value)) (some j) (memory, (ctx, c))) w ∨
        (P (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
            (ts.set i (K value)) (some j) (memory, (ctx, c))) w ∧
          match q with
          | .A => ∀ j : Fin (n + 1), quntil q P Q (interp_schedule_nd sh (n + 1)
              (ts.set i (K value)) (some j) (memory, (ctx, c))) w
          | .E => ∃ j : Fin (n + 1), quntil q P Q (interp_schedule_nd sh (n + 1)
              (ts.set i (K value)) (some j) (memory, (ctx, c))) w)) :=
  fun h0 => (quntil_sb hP hQ (nd_var_select n ts i name value K memory ctx c h0)).trans
    (quntil_brSn_iff hlive)

theorem ag_csl_nd_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    Ctx.lookup name ctx = some value →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
          (ts.set i (K value)) (some j) (memory, (ctx, c))) w ∧
        ∀ j : Fin (n + 1), entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
          (ts.set i (K value)) (some j) (memory, (ctx, c))) w) :=
  fun h0 => (proper_entails_meq _
    (interp_nd_var n ts i name value K (memory, (ctx, c)) h0)).trans
    (ag_csl_nd_select n memory ctx c _ w φ)

theorem eg_csl_nd_exp_var (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (value : Nat) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) :
    Ctx.lookup name ctx = some value →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails φ (CTree.brSn (n + 1) fun j : Fin (n + 1) => interp_schedule_nd sh (n + 1)
          (ts.set i (K value)) (some j) (memory, (ctx, c))) w ∧
        ∃ j : Fin (n + 1), entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
          (ts.set i (K value)) (some j) (memory, (ctx, c))) w) :=
  fun h0 => (proper_entails_meq _
    (interp_nd_var n ts i name value K (memory, (ctx, c)) h0)).trans
    (eg_csl_nd_select n memory ctx c _ w φ)

/-! ### exp_var_missing -/

theorem x_csl_nd_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = none →
    (qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔ False) :=
  fun h0 => (qnext_sb hP hQ (interp_nd_var_missing n ts i name K (memory, (ctx, c)) h0)).trans
    (qnext_dead_iff stuck_dead)

theorem u_csl_nd_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    Ctx.lookup name ctx = none →
    (quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔ Q (.stuck : TN) w) :=
  fun h0 => (quntil_sb hP hQ (interp_nd_var_missing n ts i name K (memory, (ctx, c)) h0)).trans
    (quntil_dead_iff stuck_dead)

theorem ag_csl_nd_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    Ctx.lookup name ctx = none →
    (entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => ag_dead stuck_dead
    ((proper_entails_meq _ (interp_nd_var_missing n ts i name K (memory, (ctx, c)) h0)).1 H)

theorem eg_csl_nd_exp_var_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (name : String) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    Ctx.lookup name ctx = none →
    (entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.var name) >>= K))
        (some i) (memory, (ctx, c))) w ↔ False) :=
  fun h0 => iff_false_intro fun H => eg_dead stuck_dead
    ((proper_entails_meq _ (interp_nd_var_missing n ts i name K (memory, (ctx, c)) h0)).1 H)

/-! ### exp_plus, exp_minus, exp_mult -/

theorem x_csl_nd_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_plus]

theorem u_csl_nd_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_plus]

theorem ag_csl_nd_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_plus]

theorem eg_csl_nd_exp_plus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.plus ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_plus]

theorem x_csl_nd_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_minus]

theorem u_csl_nd_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.minus ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_minus]

theorem ag_csl_nd_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_minus]

theorem eg_csl_nd_exp_minus (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp (.minus ea eb) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_minus]

theorem x_csl_nd_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_mult]

theorem u_csl_nd_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (_hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (_hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_mult]

theorem ag_csl_nd_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .A φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .A φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_mult]

theorem eg_csl_nd_exp_mult (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ea eb : CExp) (K : Nat → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) :
    entails (.cg .E φ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_exp (.mult ea eb) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cg .E φ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)))
        (some i) (memory, (ctx, c))) w :=
  by rw [interp_nd_source_exp_mult]

/-! ### guard (next and until only) -/

theorem x_csl_nd_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i (.guard t)) (some i)
        (memory, (ctx, c))) w ↔
      qnext q P Q (interp_schedule_nd sh (n + 1) (ts.set i t) (some i) (memory, (ctx, c))) w :=
  qnext_sb hP hQ (interp_nd_source_guard n ts i t _)

theorem u_csl_nd_guard (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (q : Ticlq) (P Q : TN → World WN → Prop) (hP : SbProper P)
    (_hlive : ∀ t w, P t w → NotDone w) (hQ : SbProper Q) :
    quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i (.guard t)) (some i)
        (memory, (ctx, c))) w ↔
      quntil q P Q (interp_schedule_nd sh (n + 1) (ts.set i t) (some i) (memory, (ctx, c))) w :=
  quntil_sb hP hQ (interp_nd_source_guard n ts i t _)

/-! ## Formula-level corollaries used downstream (`U`) -/

section Corollaries
variable {o : Option Type}

private theorem sb_entails {o : Option Type} (φ : Ticl WN o) : SbProper (entails (X := PUnit × SSig)
    (B := Bn) φ) :=
  fun _ h => proper_entails_meq φ h

theorem au_csl_nd_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (a : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) (ψ : Ticl WN o) :
    h a = none →
    (entails (.cu .A φ ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.read a) >>= K)) (some i) ((h, allocs), (ctx, c))) w ↔
      entails ψ (.stuck : TN) w) :=
  u_csl_nd_read_missing n ts i a K h allocs ctx c w .A _ _ (sb_entails φ)
    (fun _ _ => ticl_not_done φ) (sb_entails ψ)

theorem eu_csl_nd_emit (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (tag value : Nat) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) (ψ : Ticl WN o) :
    entails (.cu .E φ ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.emit tag value) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails ψ (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
          interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
            (memory, (ctx, c + 1))) w ∨
        (entails φ (log (CSLObs.emit (stamp (tag, value) c) : CSLObs (Nat × Nat)) >>= fun _ =>
            interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory, (ctx, c + 1))) w ∧
          entails (.cu .E φ ψ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
              (memory, (ctx, c + 1)))
            (.obs (E := WN) (CSLObs.emit (stamp (tag, value) c)) ⟨⟩)) :=
  u_csl_nd_emit n ts i tag value K memory ctx c w .E _ _ (sb_entails φ)
    (fun _ _ => ticl_not_done φ) (sb_entails ψ)

theorem au_csl_nd_fork (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (child : CProg Unit) (K : Option Unit → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx)
    (c : Nat) (w : World WN) (φ : TiclL WN) (ψ : Ticl WN o) :
    entails (.cu .A φ ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.fork child) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cu .A φ ψ) (interp_schedule_nd sh (n + 2)
        (Vector.cons (denote_flow child >>= fun _ => K none) (ts.set i (K (some ()))))
        (some i.succ) (memory, (ctx, c))) w :=
  u_csl_nd_fork n ts i child K memory ctx c w .A _ _ (sb_entails φ)
    (fun _ _ => ticl_not_done φ) (sb_entails ψ)

theorem au_csl_nd_ret {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (x : A) (K : Option A → Thread sE Bn) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World WN) (φ : TiclL WN) (ψ : Ticl WN o) :
    entails (.cu .A φ ψ) (interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (.ret x) >>= K))
        (some i) (memory, (ctx, c))) w ↔
      entails (.cu .A φ ψ) (interp_schedule_nd sh (n + 1) (ts.set i (K (some x))) (some i)
        (memory, (ctx, c))) w :=
  u_csl_nd_ret n ts i x K memory ctx c w .A _ _ (sb_entails φ)
    (fun _ _ => ticl_not_done φ) (sb_entails ψ)

theorem au_csl_nd_bind {A B : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (next : A → CProg B) (K : Option B → Thread sE Bn) (memory : ManagedHeap)
    (ctx : Ctx) (c : Nat) (w : World WN) (φ : TiclL WN) (ψ : Ticl WN o) :
    entails (.cu .A φ ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.bind p next) >>= K)) (some i) (memory, (ctx, c))) w ↔
      entails (.cu .A φ ψ) (interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow p >>= fun flow =>
          match flow with
          | none => K none
          | some x => denote_flow (next x) >>= K))
        (some i) (memory, (ctx, c))) w :=
  u_csl_nd_bind n ts i p next K memory ctx c w .A _ _ (sb_entails φ)
    (fun _ _ => ticl_not_done φ) (sb_entails ψ)

end Corollaries

/-! Not ported (covered by kernel `x_csl_nd_<sfx>` / `u_csl_nd_<sfx>` at `q := .A/.E` with
`P := entails φ`, `Q := entails ψ`, or `φ := ⊤` for the `ax/ex/af/ef` forms; names not in the
downstream-use set `U`): for every suffix `<sfx>` in `read, read_missing, write, write_missing,
emit, yield, fork, ret, bind, alloc_first, alloc, alloc_zero, alloc_no_space, free, free_invalid,
cas, cas_value, cas_missing, eval, assign, if, until_none_unfold, while_unfold, exp_lit, exp_var,
exp_var_missing, exp_plus, exp_minus, exp_mult, guard`, the Rocq lemmas
`an_csl_nd_<sfx> en_csl_nd_<sfx> au_csl_nd_<sfx> eu_csl_nd_<sfx> ax_csl_nd_<sfx> ex_csl_nd_<sfx>
af_csl_nd_<sfx> ef_csl_nd_<sfx>`, except `au_csl_nd_{read_missing,fork,ret,bind}` and
`eu_csl_nd_emit` (ported above); `an/au_csl_nd_{emit,yield}` and `ag_csl_nd_{emit,yield}` are in
`Lang.CoCSL.Early`. `ag/eg_csl_nd_guard` do not exist in Rocq. -/

end CoCSL
