/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Frame

/-!
# The separation layer for two active queues

Statements about heaps only (no temporal formula, no ctree): `foreign_pres` (a step of one queue
preserves the other queue's representation), `compose3` (queue 1 ⋆ queue 2 ⋆ outer frame,
reusing `qrepX_frame` unchanged), and `owned_queues_sound` (precise separating ownership of two
queues yields both representations and footprint disjointness)
(← `examples/CSL/Queue/Separation.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Separation
open Tisl Tisl.Heap Tisl.Pcm
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Trace Examples.CSL.Queue.Frame

/-! ## Footprint disjointness of two queues -/

def Disj (u : Nat) (n1 : List Nat) (v : Nat) (n2 : List Nat) : Prop :=
  ∀ x, x ∈ qcells u n1 → x ∉ qcells v n2

theorem Disj_sym (u : Nat) (n1 : List Nat) (v : Nat) (n2 : List Nat) :
    Disj u n1 v n2 → Disj v n2 u n1 := fun H x hx hy => H x hy hx

/-- The footprint is stable as a set under rotation, so disjointness is transported. -/
theorem Disj_rotl_l (u : Nat) (n1 : List Nat) (v : Nat) (n2 : List Nat) :
    n1 ≠ [] → Disj u n1 v n2 → Disj u (rotl n1) v n2 := fun hne H x hx =>
  H x ((qcells_rotl u n1 x hne).1 hx)

theorem Disj_rotl_r (u : Nat) (n1 : List Nat) (v : Nat) (n2 : List Nat) :
    n2 ≠ [] → Disj u n1 v n2 → Disj u n1 v (rotl n2) := fun hne H x hx hy =>
  H x hx ((qcells_rotl v n2 x hne).1 hy)

/-! ## The foreign step preserves the other queue -/

theorem qstep_null (u : Nat) (n1 vs1 : List Nat) (h : Heap) :
    qrep u n1 vs1 h → n1 ≠ [] → qstep u n1 h 0 = none := fun hq hne => by
  rw [qstep_agree u n1 vs1 h hq hne 0 (qwf_zero _ _ hq.1)]
  exact qrep_null _ _ _ _ hq

theorem foreign_pres (u : Nat) (n1 vs1 : List Nat) (v : Nat) (n2 vs2 : List Nat) (h : Heap) :
    qrep u n1 vs1 h → n1 ≠ [] → qrep v n2 vs2 h → Disj u n1 v n2 →
      qrep v n2 vs2 (qstep u n1 h) := fun hq1 hne1 hq2 hd =>
  qrep_agree_fp _ _ _ _ _ hq2
    (fun x hx => qstep_agree u n1 vs1 h hq1 hne1 x fun c => hd x c hx)
    (qstep_null _ _ _ _ hq1 hne1)

/-- The same statement in the `rot_heap` form the language layer produces. -/
theorem foreign_pres_rot (u a : Nat) (n1 vs1 : List Nat) (v : Nat) (n2 vs2 : List Nat)
    (h : Heap) :
    qrep u (a :: n1) vs1 h → qrep v n2 vs2 h → Disj u (a :: n1) v n2 →
      qrep v n2 vs2 (rot_heap u a (n1.headD 0) (zof u n1) h) := fun hq1 hq2 hd =>
  foreign_pres u (a :: n1) vs1 v n2 vs2 h hq1 (by simp) hq2 hd

/-! ## Three-way composition: queue 1 ⋆ queue 2 ⋆ outer frame -/

theorem compose3 (u : Nat) (n1 vs1 : List Nat) (h1 : Heap) (v : Nat) (n2 vs2 : List Nat)
    (h2 f : Heap) :
    qrepX u n1 vs1 h1 → qrepX v n2 vs2 h2 → hdisj h1 h2 → hdisj h1 f → hdisj h2 f →
      f 0 = none →
      qrep u n1 vs1 (hunion h1 (hunion h2 f)) ∧ qrep v n2 vs2 (hunion h1 (hunion h2 f)) ∧
        Disj u n1 v n2 := by
  intro hx1 hx2 h12 h1f _ hf0
  have hq1 := qrepX_qrep _ _ _ _ hx1
  have hq2 := qrepX_qrep _ _ _ _ hx2
  have hun0 : hunion h2 f 0 = none := hunion_null _ _ (qrep_null _ _ _ _ hq2) hf0
  refine ⟨qrepX_frame u n1 vs1 h1 (hunion h2 f) hx1 (hdisj_union h1 h2 f h12 h1f) hun0, ?_,
    fun x hx1' hx2' => ?_⟩
  · refine qrep_agree_fp _ _ _ _ _ hq2 (fun x hx => ?_) ?_
    · have hd2 := qrep_fp _ _ _ _ hq2 x hx
      rw [hunion_none _ _ _ ((h12 x).resolve_right hd2), hunion_eq _ _ _ hd2]
    · rw [hunion_none _ _ _ (qrep_null _ _ _ _ hq1)]; exact hun0
  · rcases h12 x with e | e
    · exact qrep_fp _ _ _ _ hq1 x hx1' e
    · exact qrep_fp _ _ _ _ hq2 x hx2' e

/-! ## Precise ownership of two queues -/

def owned_queues (u : Nat) (ns1 vs1 : List Nat) (v : Nat) (ns2 vs2 : List Nat) : Heap → Prop :=
  asep (qrepX u ns1 vs1) (qrepX v ns2 vs2)

theorem owned_queues_sound (u : Nat) (ns1 vs1 : List Nat) (v : Nat) (ns2 vs2 : List Nat)
    (h : Heap) :
    owned_queues u ns1 vs1 v ns2 vs2 h →
      qrep u ns1 vs1 h ∧ qrep v ns2 vs2 h ∧ Disj u ns1 v ns2 := by
  rintro ⟨h1, h2, hd, heqh, H1, H2⟩
  change hdisj h1 h2 at hd
  change heq h (hunion h1 h2) at heqh
  obtain ⟨Q1, Q2, hdj⟩ := compose3 u ns1 vs1 h1 v ns2 vs2 h2 hemp H1 H2 hd
    (fun _ => .inr rfl) (fun _ => .inr rfl) rfl
  have hagree : ∀ x, hunion h1 (hunion h2 hemp) x = h x := by
    intro x; rw [heqh]; unfold hunion hemp
    cases h1 x <;> simp; cases h2 x <;> rfl
  refine ⟨qrep_agree_fp _ _ _ _ _ Q1 (fun x _ => (hagree x).symm) ?_,
    qrep_agree_fp _ _ _ _ _ Q2 (fun x _ => (hagree x).symm) ?_, hdj⟩
  · rw [← hagree]; exact qrep_null _ _ _ _ Q1
  · rw [← hagree]; exact qrep_null _ _ _ _ Q2

end Examples.CSL.Queue.Separation
