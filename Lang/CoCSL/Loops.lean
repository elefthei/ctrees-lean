/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Early
public import Logic.CTree.Iter

/-!
# CoCSL actual-run loop rules

Well-founded `AU`/`EU`/`AF`/`EF` and coinductive `AG`/`EG` rules for `untilNone` and `while` loops
focused in an actual scheduled pool. A configuration is a pool size, pool, focus and state (plus
the actual, possibly changed, cursor under round robin); a finite segment of one loop iteration
either establishes the target or reaches a bisimilar loop configuration (← `Lang/CoCSL/Mod.v`,
lines 2205-3625).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Notation
open ITree (Effect)

/-! ## Generic cutpoint families over configurations -/

section Generic
variable {W C G : Type} {o : Option Type}

private theorem quntil_mono_r {q : Ticlq} {P Q Q' : ctreeW W Bn (PUnit × SSig) →
    World (writerE W) → Prop} (h : ∀ t w, Q t w → Q' t w) :
    ∀ t w, quntil q P Q t w → quntil q P Q' t w := by
  cases q
  · exact auc_mono_r h
  · exact euc_mono_r h

private theorem qnext_mono_r {q : Ticlq} {P Q Q' : ctreeW W Bn (PUnit × SSig) →
    World (writerE W) → Prop} (h : ∀ t w, Q t w → Q' t w) :
    ∀ t w, qnext q P Q t w → qnext q P Q' t w := by
  cases q
  · exact anc_mono_r h
  · exact enc_mono_r h

/-- Until over ranked configurations: `T c` is the focused loop, `U c` its one-iteration
unfolding (equal trees). -/
private theorem u_loop_wf (q : Ticlq) (T U : C → ctreeW W Bn (PUnit × SSig))
    (hshape : T = U) (Inv : G → C → World (writerE W) → Prop) (ltG : G → G → Prop)
    (φ : TiclL (writerE W)) (ψ : Ticl (writerE W) o) (hwf : WellFounded ltG)
    (hbody : ∀ g c w, Inv g c w →
      quntil q (entails φ)
        (fun t z => entails ψ t z ∨ ∃ g' c', Inv g' c' z ∧ ltG g' g ∧ t ~ T c') (U c) w)
    (g : G) (c : C) (w : World (writerE W)) (hinv : Inv g c w) :
    entails (.cu q φ ψ) (T c) w := by
  subst hshape
  have hwf' : WellFounded fun (a b : (G × C) × World (writerE W)) => ltG a.1.1 b.1.1 :=
    InvImage.wf _ hwf
  have hbody' := fun (p : G × C) w h => quntil_mono_r (fun t z h => h.imp_right
      fun ⟨g', c', hi, hl, ht⟩ => (⟨(g', c'), hi, hl, ht⟩ :
        ∃ j : G × C, Inv j.1 j.2 z ∧ ltG j.1 p.1 ∧ t ~ T j.2)) _ _ (hbody p.1 p.2 w h)
  cases q
  · exact au_family_wf (fun p : G × C => T p.2) (fun p => T p.2) (fun p => Inv p.1 p.2) _
      (fun _ => sbisim_refl _) hwf' hbody' (g, c) w hinv
  · exact eu_family_wf (fun p : G × C => T p.2) (fun p => T p.2) (fun p => Inv p.1 p.2) _
      (fun _ => sbisim_refl _) hwf' hbody' (g, c) w hinv

/-- Global invariance over configurations; the leading next forces progress before reentry. -/
private theorem g_loop (q : Ticlq) (T U : C → ctreeW W Bn (PUnit × SSig)) (hshape : T = U)
    (Inv : G → C → World (writerE W) → Prop) (φ : TiclL (writerE W))
    (hbody : ∀ g c w, Inv g c w →
      qnext q (entails φ)
        (quntil q (entails φ)
          (fun t z => (∃ g' c', Inv g' c' z ∧ t ~ T c') ∨ entails (.cg q φ) t z))
        (U c) w)
    (g : G) (c : C) (w : World (writerE W)) (hinv : Inv g c w) :
    entails (.cg q φ) (T c) w := by
  subst hshape
  have hbody' := fun (p : G × C) w h => qnext_mono_r (quntil_mono_r fun t z h => h.imp_left
      fun ⟨g', c', hi, ht⟩ => (⟨(g', c'), hi, ht⟩ : ∃ j : G × C, Inv j.1 j.2 z ∧ t ~ T j.2))
    _ _ (hbody p.1 p.2 w h)
  cases q
  · exact ag_family (fun p : G × C => T p.2) (fun p => T p.2) (fun p => Inv p.1 p.2)
      (fun _ => sbisim_refl _) hbody' (g, c) w hinv
  · exact eg_family (fun p : G × C => T p.2) (fun p => T p.2) (fun p => Inv p.1 p.2)
      (fun _ => sbisim_refl _) hbody' (g, c) w hinv

end Generic

/-! ## Scheduler instances

A configuration is Rocq's dependent `{ n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig)) }`
(round robin: `… * (nat * SSig)`); the loop thread is fixed and only the configuration varies. -/

section Runners
variable {G : Type} {o : Option Type}

private theorem u_nd_loop_wf (q : Ticlq) (loop unf : Thread sE Bn) (hshape : loop = unf)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) (hwf : WellFounded ltG)
    (hbody : ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil q (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1)) (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1) (ts'.set i' loop) (some i') σ')
        (interp_schedule_nd sh (n + 1) (ts.set i unf) (some i) σ) w)
    (g : G) (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (σ : SSig) w
    (hinv : Inv g n ts i σ w) :
    entails (.cu q φ ψ) (interp_schedule_nd sh (n + 1) (ts.set i loop) (some i) σ) w :=
  u_loop_wf q
    (fun c : (n : Nat) × Pool sE Bn (n + 1) × Fin (n + 1) × SSig =>
      interp_schedule_nd sh (c.1 + 1) (c.2.1.set c.2.2.1 loop) (some c.2.2.1) c.2.2.2)
    (fun c => interp_schedule_nd sh (c.1 + 1) (c.2.1.set c.2.2.1 unf) (some c.2.2.1) c.2.2.2)
    (by rw [hshape]) (fun g c => Inv g c.1 c.2.1 c.2.2.1 c.2.2.2) ltG φ ψ hwf
    (fun g c w h => quntil_mono_r (fun _ _ h => h.imp_right
        fun ⟨g', n', ts', i', σ', hi, hl, ht⟩ => ⟨g', ⟨n', ts', i', σ'⟩, hi, hl, ht⟩) _ _
      (hbody g c.1 c.2.1 c.2.2.1 c.2.2.2 w h))
    g ⟨n, ts, i, σ⟩ w hinv

private theorem u_rr_loop_wf (q : Ticlq) (loop unf : Thread sE Bn) (hshape : loop = unf)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) (hwf : WellFounded ltG)
    (hbody : ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w,
      Inv g n ts i cursor σ w →
      quntil q (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1) (ts'.set i' loop) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1) (ts.set i unf) (some i) cursor σ) w)
    (g : G) (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (cursor : Nat) (σ : SSig) w
    (hinv : Inv g n ts i cursor σ w) :
    entails (.cu q φ ψ) (interp_schedule_rr sh (n + 1) (ts.set i loop) (some i) cursor σ) w :=
  u_loop_wf q
    (fun c : (n : Nat) × Pool sE Bn (n + 1) × Fin (n + 1) × Nat × SSig =>
      interp_schedule_rr sh (c.1 + 1) (c.2.1.set c.2.2.1 loop) (some c.2.2.1) c.2.2.2.1
        c.2.2.2.2)
    (fun c => interp_schedule_rr sh (c.1 + 1) (c.2.1.set c.2.2.1 unf) (some c.2.2.1) c.2.2.2.1
        c.2.2.2.2)
    (by rw [hshape]) (fun g c => Inv g c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2) ltG φ ψ hwf
    (fun g c w h => quntil_mono_r (fun _ _ h => h.imp_right
        fun ⟨g', n', ts', i', cursor', σ', hi, hl, ht⟩ =>
          ⟨g', ⟨n', ts', i', cursor', σ'⟩, hi, hl, ht⟩) _ _
      (hbody g c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 w h))
    g ⟨n, ts, i, cursor, σ⟩ w hinv

private theorem g_nd_loop (q : Ticlq) (loop unf : Thread sE Bn) (hshape : loop = unf)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (hbody : ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      qnext q (entails φ)
        (quntil q (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1)) (σ' : SSig),
              Inv g' n' ts' i' σ' z ∧
              t ~ interp_schedule_nd sh (n' + 1) (ts'.set i' loop) (some i') σ') ∨
            entails (.cg q φ) t z))
        (interp_schedule_nd sh (n + 1) (ts.set i unf) (some i) σ) w)
    (g : G) (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (σ : SSig) w
    (hinv : Inv g n ts i σ w) :
    entails (.cg q φ) (interp_schedule_nd sh (n + 1) (ts.set i loop) (some i) σ) w :=
  g_loop q
    (fun c : (n : Nat) × Pool sE Bn (n + 1) × Fin (n + 1) × SSig =>
      interp_schedule_nd sh (c.1 + 1) (c.2.1.set c.2.2.1 loop) (some c.2.2.1) c.2.2.2)
    (fun c => interp_schedule_nd sh (c.1 + 1) (c.2.1.set c.2.2.1 unf) (some c.2.2.1) c.2.2.2)
    (by rw [hshape]) (fun g c => Inv g c.1 c.2.1 c.2.2.1 c.2.2.2) φ
    (fun g c w h => qnext_mono_r (quntil_mono_r fun _ _ h => h.imp_left
        fun ⟨g', n', ts', i', σ', hi, ht⟩ => ⟨g', ⟨n', ts', i', σ'⟩, hi, ht⟩) _ _
      (hbody g c.1 c.2.1 c.2.2.1 c.2.2.2 w h))
    g ⟨n, ts, i, σ⟩ w hinv

private theorem g_rr_loop (q : Ticlq) (loop unf : Thread sE Bn) (hshape : loop = unf)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (hbody : ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w,
      Inv g n ts i cursor σ w →
      qnext q (entails φ)
        (quntil q (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (cursor' : Nat) (σ' : SSig),
              Inv g' n' ts' i' cursor' σ' z ∧
              t ~ interp_schedule_rr sh (n' + 1) (ts'.set i' loop) (some i') cursor' σ') ∨
            entails (.cg q φ) t z))
        (interp_schedule_rr sh (n + 1) (ts.set i unf) (some i) cursor σ) w)
    (g : G) (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (cursor : Nat) (σ : SSig) w
    (hinv : Inv g n ts i cursor σ w) :
    entails (.cg q φ) (interp_schedule_rr sh (n + 1) (ts.set i loop) (some i) cursor σ) w :=
  g_loop q
    (fun c : (n : Nat) × Pool sE Bn (n + 1) × Fin (n + 1) × Nat × SSig =>
      interp_schedule_rr sh (c.1 + 1) (c.2.1.set c.2.2.1 loop) (some c.2.2.1) c.2.2.2.1
        c.2.2.2.2)
    (fun c => interp_schedule_rr sh (c.1 + 1) (c.2.1.set c.2.2.1 unf) (some c.2.2.1) c.2.2.2.1
        c.2.2.2.2)
    (by rw [hshape]) (fun g c => Inv g c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2) φ
    (fun g c w h => qnext_mono_r (quntil_mono_r fun _ _ h => h.imp_left
        fun ⟨g', n', ts', i', cursor', σ', hi, ht⟩ => ⟨g', ⟨n', ts', i', cursor', σ'⟩, hi, ht⟩)
      _ _ (hbody g c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 w h))
    g ⟨n, ts, i, cursor, σ⟩ w hinv

end Runners

/-! ## Nondeterministic `untilNone` -/

theorem au_csl_nd_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .A (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (φ AU ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .A _ _ (source_raw_until body K) Inv ltG φ ψ

theorem eu_csl_nd_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .E (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (φ EU ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .E _ _ (source_raw_until body K) Inv ltG φ ψ

theorem af_csl_nd_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .A (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (AF ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .A _ _ (source_raw_until body K) Inv ltG _ ψ

theorem ef_csl_nd_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .E (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (EF ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .E _ _ (source_raw_until body K) Inv ltG _ ψ

theorem ag_csl_nd_until_none {A G : Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat)))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      qnext .A (entails φ)
        (quntil .A (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (σ' : SSig),
              Inv g' n' ts' i' σ' z ∧
              t ~ interp_schedule_nd sh (n' + 1)
                  (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') σ') ∨
            entails (AG φ) t z))
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (AG φ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) σ) w :=
  g_nd_loop .A _ _ (source_raw_until body K) Inv φ

theorem eg_csl_nd_until_none {A G : Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat)))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      qnext .E (entails φ)
        (quntil .E (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (σ' : SSig),
              Inv g' n' ts' i' σ' z ∧
              t ~ interp_schedule_nd sh (n' + 1)
                  (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') σ') ∨
            entails (EG φ) t z))
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (EG φ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) σ) w :=
  g_nd_loop .E _ _ (source_raw_until body K) Inv φ

/-! ## Nondeterministic `while` -/

theorem au_csl_nd_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .A (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (φ AU ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .A _ _ (source_raw_while_unfold test body K) Inv ltG φ ψ

theorem eu_csl_nd_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .E (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (φ EU ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .E _ _ (source_raw_while_unfold test body K) Inv ltG φ ψ

theorem af_csl_nd_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .A (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (AF ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .A _ _ (source_raw_while_unfold test body K) Inv ltG _ ψ

theorem ef_csl_nd_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      quntil .E (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (σ' : SSig),
            Inv g' n' ts' i' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_nd sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') σ')
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (EF ψ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) σ) w :=
  u_nd_loop_wf .E _ _ (source_raw_while_unfold test body K) Inv ltG _ ψ

theorem ag_csl_nd_while {G : Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat)))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      qnext .A (entails φ)
        (quntil .A (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (σ' : SSig),
              Inv g' n' ts' i' σ' z ∧
              t ~ interp_schedule_nd sh (n' + 1)
                  (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') σ') ∨
            entails (AG φ) t z))
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (AG φ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) σ) w :=
  g_nd_loop .A _ _ (source_raw_while_unfold test body K) Inv φ

theorem eg_csl_nd_while {G : Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → SSig →
      World (writerE (CSLObs (Nat × Nat))) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat)))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      qnext .E (entails φ)
        (quntil .E (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (σ' : SSig),
              Inv g' n' ts' i' σ' z ∧
              t ~ interp_schedule_nd sh (n' + 1)
                  (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') σ') ∨
            entails (EG φ) t z))
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) σ w, Inv g n ts i σ w →
      entails (EG φ)
        (interp_schedule_nd sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) σ) w :=
  g_nd_loop .E _ _ (source_raw_while_unfold test body K) Inv φ

/-! ## Round robin `untilNone` -/

theorem au_csl_rr_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .A (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (φ AU ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .A _ _ (source_raw_until body K) Inv ltG φ ψ

theorem eu_csl_rr_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .E (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (φ EU ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .E _ _ (source_raw_until body K) Inv ltG φ ψ

theorem af_csl_rr_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .A (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (AF ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .A _ _ (source_raw_until body K) Inv ltG _ ψ

theorem ef_csl_rr_until_none_wf {A G : Type} {o : Option Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .E (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (EF ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .E _ _ (source_raw_until body K) Inv ltG _ ψ

theorem ag_csl_rr_until_none {A G : Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      qnext .A (entails φ)
        (quntil .A (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (cursor' : Nat) (σ' : SSig),
              Inv g' n' ts' i' cursor' σ' z ∧
              t ~ interp_schedule_rr sh (n' + 1)
                  (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') cursor' σ') ∨
            entails (AG φ) t z))
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (AG φ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) cursor σ) w :=
  g_rr_loop .A _ _ (source_raw_until body K) Inv φ

theorem eg_csl_rr_until_none {A G : Type}
    (body : CProg (Option A)) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      qnext .E (entails φ)
        (quntil .E (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (cursor' : Nat) (σ' : SSig),
              Inv g' n' ts' i' cursor' σ' z ∧
              t ~ interp_schedule_rr sh (n' + 1)
                  (ts'.set i' (denote_flow (.untilNone body) >>= K)) (some i') cursor' σ') ∨
            entails (EG φ) t z))
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow body >>= until_tail body K))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (EG φ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.untilNone body) >>= K)) (some i) cursor σ) w :=
  g_rr_loop .E _ _ (source_raw_until body K) Inv φ

/-! ## Round robin `while` -/

theorem au_csl_rr_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .A (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (φ AU ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .A _ _ (source_raw_while_unfold test body K) Inv ltG φ ψ

theorem eu_csl_rr_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .E (entails φ)
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (φ EU ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .E _ _ (source_raw_while_unfold test body K) Inv ltG φ ψ

theorem af_csl_rr_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .A (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (AF ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .A _ _ (source_raw_while_unfold test body K) Inv ltG _ ψ

theorem ef_csl_rr_while_wf {G : Type} {o : Option Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (ltG : G → G → Prop)
    (ψ : Ticl (writerE (CSLObs (Nat × Nat) ⊕ Nat)) o) :
    WellFounded ltG →
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      quntil .E (entails (.now fun _ => True))
        (fun t z => entails ψ t z ∨
          ∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
            (cursor' : Nat) (σ' : SSig),
            Inv g' n' ts' i' cursor' σ' z ∧ ltG g' g ∧
            t ~ interp_schedule_rr sh (n' + 1)
                (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') cursor' σ')
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (EF ψ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) cursor σ) w :=
  u_rr_loop_wf .E _ _ (source_raw_while_unfold test body K) Inv ltG _ ψ

theorem ag_csl_rr_while {G : Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      qnext .A (entails φ)
        (quntil .A (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (cursor' : Nat) (σ' : SSig),
              Inv g' n' ts' i' cursor' σ' z ∧
              t ~ interp_schedule_rr sh (n' + 1)
                  (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') cursor' σ') ∨
            entails (AG φ) t z))
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (AG φ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) cursor σ) w :=
  g_rr_loop .A _ _ (source_raw_while_unfold test body K) Inv φ

theorem eg_csl_rr_while {G : Type}
    (test : CExp) (body : CProg Unit) (K : Option Unit → Thread sE Bn)
    (Inv : G → ∀ n, Pool sE Bn (n + 1) → Fin (n + 1) → Nat → SSig →
      World (writerE (CSLObs (Nat × Nat) ⊕ Nat)) → Prop)
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    (∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      qnext .E (entails φ)
        (quntil .E (entails φ)
          (fun t z =>
            (∃ (g' : G) (n' : Nat) (ts' : Pool sE Bn (n' + 1)) (i' : Fin (n' + 1))
              (cursor' : Nat) (σ' : SSig),
              Inv g' n' ts' i' cursor' σ' z ∧
              t ~ interp_schedule_rr sh (n' + 1)
                  (ts'.set i' (denote_flow (.while test body) >>= K)) (some i') cursor' σ') ∨
            entails (EG φ) t z))
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_exp test >>= fun value =>
                if is_true value then
                  denote_flow body >>= fun flow =>
                    match flow with
                    | none => K none
                    | some _ => .guard (denote_flow (.while test body) >>= K)
                else K (some ())))
            (some i) cursor σ) w) →
    ∀ g n (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) cursor σ w, Inv g n ts i cursor σ w →
      entails (EG φ)
        (interp_schedule_rr sh (n + 1)
            (ts.set i (denote_flow (.while test body) >>= K)) (some i) cursor σ) w :=
  g_rr_loop .E _ _ (source_raw_while_unfold test body K) Inv φ

-- Not ported: nothing. The proof-local configuration sigma types, trees `T`/`U`, invariant `J`
-- and lifted rank `Rv` of the Rocq proofs are the private `u_loop_wf`/`g_loop` helpers.

end CoCSL
