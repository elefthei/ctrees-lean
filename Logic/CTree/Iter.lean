/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Bind
public import Logic.CTree.Ret

/-!
# Iteration rules on ctrees

Structural loop rules for `CTree.iter`/`CTree.iterS`: well-founded cutpoint families for `AU`/`EU`,
coinductive families for `AG`/`EG`, continuation-parametric rules, prefix iteration, return-driven
iteration with well-founded or natural-number ranks, and loop invariants for `AG`/`EG`
(← `CTree/Logic/Iter.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinduction Notation
open ITree (Effect)

section IterLemmas
variable {E B : Effect.{u}} {X I : Type u} {o : Option (Type u)}

/-! ## Cutpoint families -/

/-- Actual-run cutpoints for `AU`: finite body segments either establish the target or reach a
bisimilar family member at a strictly smaller configuration. -/
theorem au_family_wf (T Body : I → CTree E B X) (Inv : I → World E → Prop)
    (Rv : I × World E → I × World E → Prop) {φ : TiclL E} {ψ : Ticl E o}
    (hshape : ∀ i, T i ~ Body i) (hwf : WellFounded Rv)
    (hbody : ∀ i w, Inv i w →
      Auc (entails φ)
        (fun t z => entails ψ t z ∨ ∃ j, Inv j z ∧ Rv (j, z) (i, w) ∧ t ~ T j) (Body i) w) :
    ∀ i w, Inv i w → entails (φ AU ψ) (T i) w := by
  intro i w hinv
  refine hwf.induction (C := fun p => Inv p.1 p.2 → entails (φ AU ψ) (T p.1) p.2) (i, w) ?_ hinv
  rintro ⟨i, w⟩ ih hinv
  refine (proper_entails_meq (φ AU ψ) (hshape i)).2 (auc_join _ _ ?_)
  refine auc_mono_r (fun t z h => ?_) _ _ (hbody i w hinv)
  rcases h with h | ⟨j, hj, hv, ht⟩
  · exact .matchA h
  · exact (proper_entails_meq (φ AU ψ) ht).2 (ih (j, z) hv hj)

/-- Actual-run cutpoints for `EU`. -/
theorem eu_family_wf (T Body : I → CTree E B X) (Inv : I → World E → Prop)
    (Rv : I × World E → I × World E → Prop) {φ : TiclL E} {ψ : Ticl E o}
    (hshape : ∀ i, T i ~ Body i) (hwf : WellFounded Rv)
    (hbody : ∀ i w, Inv i w →
      Euc (entails φ)
        (fun t z => entails ψ t z ∨ ∃ j, Inv j z ∧ Rv (j, z) (i, w) ∧ t ~ T j) (Body i) w) :
    ∀ i w, Inv i w → entails (φ EU ψ) (T i) w := by
  intro i w hinv
  refine hwf.induction (C := fun p => Inv p.1 p.2 → entails (φ EU ψ) (T p.1) p.2) (i, w) ?_ hinv
  rintro ⟨i, w⟩ ih hinv
  refine (proper_entails_meq (φ EU ψ) (hshape i)).2 (euc_join _ _ ?_)
  refine euc_mono_r (fun t z h => ?_) _ _ (hbody i w hinv)
  rcases h with h | ⟨j, hj, hv, ht⟩
  · exact .matchE h
  · exact (proper_entails_meq (φ EU ψ) ht).2 (ih (j, z) hv hj)

/-- Finite until is closed at every stage of the final chain of `agcF P`: chain elements are
pre-fixpoints. -/
private theorem auc_family_chain {P : CTree E B X → World E → Prop}
    {R : Rel (CTree E B X) (World E)} (hR : Chain (agcF P) R) :
    ∀ t w, Auc P R t w → R t w := by
  intro t w h
  induction h with
  | matchA h => exact h
  | stepA hp hs _ ih => step; exact ⟨hp, hs, ih⟩

private theorem euc_family_chain {P : CTree E B X → World E → Prop}
    {R : Rel (CTree E B X) (World E)} (hR : Chain (egcF P) R) :
    ∀ t w, Euc P R t w → R t w := by
  intro t w h
  induction h with
  | matchE h => exact h
  | stepE t' w' hp tr _ ih => step; exact ⟨hp, t', w', tr, ih⟩

/-- `AG` cutpoint family. The leading next requires actual progress before another cutpoint; a
silent guard-only cycle is not sufficient. -/
theorem ag_family (T Body : I → CTree E B X) (Inv : I → World E → Prop) {φ : TiclL E}
    (hshape : ∀ i, T i ~ Body i)
    (hbody : ∀ i w, Inv i w →
      anc (entails φ)
        (Auc (entails φ) (fun t z => (∃ j, Inv j z ∧ t ~ T j) ∨ agc (entails φ) t z))
        (Body i) w) :
    ∀ i w, Inv i w → entails (AG φ) (T i) w := by
  have hP : SbProper (entails (X := X) (B := B) φ) := fun _ h => proper_entails_meq φ h
  coinduction R hR CIH
  intro i w hinv
  have hRp := agc_chain_proper (P := entails φ) (fun _ _ _ h => hP _ h) R hR
  refine (proper_ax_equ (P := entails φ) (Q := R) (fun _ _ _ h => hP _ h) hRp (hshape i)).2 ?_
  refine anc_mono_r (fun t z h => auc_family_chain hR t z ?_) _ _ (hbody i w hinv)
  refine auc_mono_r (fun u y h => ?_) _ _ h
  rcases h with ⟨j, hj, ht⟩ | hG
  · exact (hRp _ _ _ ht).2 (CIH j y hj)
  · exact gfp_le_chain hR _ _ hG

/-- `EG` cutpoint family. -/
theorem eg_family (T Body : I → CTree E B X) (Inv : I → World E → Prop) {φ : TiclL E}
    (hshape : ∀ i, T i ~ Body i)
    (hbody : ∀ i w, Inv i w →
      enc (entails φ)
        (Euc (entails φ) (fun t z => (∃ j, Inv j z ∧ t ~ T j) ∨ egc (entails φ) t z))
        (Body i) w) :
    ∀ i w, Inv i w → entails (EG φ) (T i) w := by
  have hP : SbProper (entails (X := X) (B := B) φ) := fun _ h => proper_entails_meq φ h
  coinduction R hR CIH
  intro i w hinv
  have hRp := egc_chain_proper (P := entails φ) (fun _ _ _ h => hP _ h) R hR
  refine (proper_ex_equ (P := entails φ) (Q := R) (fun _ _ _ h => hP _ h) hRp (hshape i)).2 ?_
  refine enc_mono_r (fun t z h => euc_family_chain hR t z ?_) _ _ (hbody i w hinv)
  refine euc_mono_r (fun u y h => ?_) _ _ h
  rcases h with ⟨j, hj, ht⟩ | hG
  · exact (hRp _ _ _ ht).2 (CIH j y hj)
  · exact gfp_le_chain hR _ _ hG

/-! ## Continuation-parametric rules -/

/-- Return-driven iteration: decreasing body leaves may converge to one native result without
requiring one immediate return. -/
theorem ret_iter_wf (Ri : I → World E → Prop) (Rv : I × World E → I × World E → Prop)
    {body : I → CTree E B (I ⊕ X)} {P : X → World E → Prop} (hwf : WellFounded Rv)
    (hbody : ∀ i w, Ri i w → ∀ cont : I → CTree E B X,
      (∀ j z, Ri j z → Rv (j, z) (i, w) → entails (.ret P) (cont j) z) →
      entails (.ret P)
        (body i >>= fun | .inl j => CTree.guard (cont j) | .inr x => pure x) w) :
    ∀ i w, Ri i w → entails (.ret P) (CTree.iter body i) w := by
  intro i w hinv
  refine hwf.induction (C := fun p => Ri p.1 p.2 → entails (.ret P) (CTree.iter body p.1) p.2)
    (i, w) ?_ hinv
  rintro ⟨i, w⟩ ih hinv
  rw [unfold_iter]
  exact hbody i w hinv _ fun j z hj hv => ih (j, z) hv hj

/-- Visible iteration retains the real `step` at every continuing leaf; both path quantifiers and
every formula index share this rule. -/
theorem u_iterS_wf {q : Ticlq} (Ri : I → World E → Prop) (Rv : I × World E → I × World E → Prop)
    {body : I → CTree E B (I ⊕ X)} {φ : TiclL E} {ψ : Ticl E o} (hwf : WellFounded Rv)
    (hbody : ∀ i w, Ri i w → ∀ cont : I → CTree E B X,
      (∀ j z, Ri j z → Rv (j, z) (i, w) → entails (.cu q φ ψ) (cont j) z) →
      entails (.cu q φ ψ)
        (body i >>= fun | .inl j => CTree.step (cont j) | .inr x => pure x) w) :
    ∀ i w, Ri i w → entails (.cu q φ ψ) (CTree.iterS body i) w := by
  intro i w hinv
  refine hwf.induction
    (C := fun p => Ri p.1 p.2 → entails (.cu q φ ψ) (CTree.iterS body p.1) p.2) (i, w) ?_ hinv
  rintro ⟨i, w⟩ ih hinv
  rw [unfold_iterS]
  exact hbody i w hinv _ fun j z hj hv => ih (j, z) hv hj

/-! ## Prefix iteration -/

/-- Prefix iteration for either next quantifier: the body either already satisfies the next
formula or returns an `inl` state along a finite `Rv`-decreasing chain. -/
theorem n_iter_prefix {q : Ticlq} (Ri : I → World E → Prop) (Rv : I → I → Prop) {i : I}
    {w : World E} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL E} (hwf : WellFounded Rv)
    (hi : Ri i w)
    (H : ∀ i w, Ri i w →
      entails (.cx q φ ψ) (k i) w ∨
        entails (.ret fun (lr : I ⊕ X) w' => ∃ i', lr = .inl i' ∧ Ri i' w' ∧ Rv i' i) (k i) w) :
    entails (.cx q φ ψ) (CTree.iter k i) w := by
  induction i using hwf.induction generalizing w with
  | _ i ih =>
  rw [unfold_iter]
  rcases H i w hi with h | h
  · exact ticll_bind_l h
  · refine ticl_bind_ret h fun lr w' ⟨j, hlr, hj, hv⟩ => ?_
    subst hlr
    exact (proper_entails_meq _ (sb_guard _)).2 (ih j hv hj)

/-- One unfolding of an until proof whose body returns a continuing state. -/
theorem u_iter_next {q : Ticlq} (R : I → World E → Prop) {i : I} {w : World E}
    {k : I → CTree E B (I ⊕ X)} {φ : TiclL E} {ψ : Ticl E o}
    (hbody : entails (.cu q φ (.ret fun (lr : I ⊕ X) w => ∃ i', lr = .inl i' ∧ R i' w)) (k i) w)
    (hnext : ∀ i w, R i w → entails (.cu q φ ψ) (CTree.iter k i) w) :
    entails (.cu q φ ψ) (CTree.iter k i) w := by
  rw [unfold_iter]
  refine u_bind_r hbody fun lr w' ⟨j, hlr, hj⟩ => ?_
  subst hlr
  exact (proper_entails_meq _ (sb_guard _)).2 (hnext j w' hj)

/-- Split liveness between an established region `Ri` and an `Rv`-decreasing continuation. -/
theorem u_iter_split {q : Ticlq} (R Ri : I → World E → Prop)
    (Rv : I × World E → I × World E → Prop) {i : I} {w : World E} {k : I → CTree E B (I ⊕ X)}
    {φ : TiclL E} {ψ : Ticl E o} (hwf : WellFounded Rv) (hd : NotDone w) (hR : R i w)
    (hregion : ∀ i w, NotDone w → Ri i w → entails (.cu q φ ψ) (CTree.iter k i) w)
    (hbody : ∀ i w, NotDone w → R i w →
      entails (.cu q φ (.ret fun (lr : I ⊕ X) w' =>
          ∃ i', lr = .inl i' ∧ NotDone w' ∧ Ri i' w')) (k i) w ∨
        entails (.cu q φ (.ret fun (lr : I ⊕ X) w' =>
          ∃ i', lr = .inl i' ∧ NotDone w' ∧ R i' w' ∧ Rv (i', w') (i, w))) (k i) w) :
    entails (.cu q φ ψ) (CTree.iter k i) w := by
  refine hwf.induction (C := fun p => NotDone p.2 → R p.1 p.2 →
    entails (.cu q φ ψ) (CTree.iter k p.1) p.2) (i, w) ?_ hd hR
  rintro ⟨i, w⟩ ih hd hR
  rcases hbody i w hd hR with h | h
  · exact u_iter_next (fun i w => NotDone w ∧ Ri i w) h fun j w' ⟨hd', hj⟩ => hregion j w' hd' hj
  · exact u_iter_next (fun j w' => NotDone w' ∧ R j w' ∧ Rv (j, w') (i, w)) h
      fun j w' ⟨hd', hj, hv⟩ => ih (j, w') hv hd' hj

/-- Direct-body prefix iteration for either until quantifier: the body either already satisfies
the prefix until formula, without having to return, or returns an `inl` state preserving the
invariant and decreasing the well-founded rank. -/
theorem u_iter_prefix {q : Ticlq} (R : I → World E → Prop)
    (Rv : I × World E → I × World E → Prop) {i : I} {w : World E} {k : I → CTree E B (I ⊕ X)}
    {φ ψ : TiclL E} (hwf : WellFounded Rv) (hd : NotDone w) (hR : R i w)
    (hbody : ∀ i w, NotDone w → R i w →
      entails (.cu q φ ψ) (k i) w ∨
        entails (.cu q φ (.ret fun (lr : I ⊕ X) w' =>
          ∃ i', lr = .inl i' ∧ NotDone w' ∧ R i' w' ∧ Rv (i', w') (i, w))) (k i) w) :
    entails (.cu q φ ψ) (CTree.iter k i) w := by
  refine hwf.induction (C := fun p => NotDone p.2 → R p.1 p.2 →
    entails (.cu q φ ψ) (CTree.iter k p.1) p.2) (i, w) ?_ hd hR
  rintro ⟨i, w⟩ ih hd hR
  rw [unfold_iter]
  rcases hbody i w hd hR with h | h
  · exact ticll_bind_l h
  · refine u_bind_r h fun lr w' ⟨j, hlr, hd', hj, hv⟩ => ?_
    subst hlr
    exact (proper_entails_meq _ (sb_guard _)).2 (ih (j, w') hv hd' hj)

/-- Natural-number ranks instantiate the direct-body prefix algorithm. -/
theorem u_iter_prefix_nat {q : Ticlq} (Ri : I → World E → Prop) (f : I → World E → Nat) {i : I}
    {w : World E} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL E} (hd : NotDone w) (hR : Ri i w)
    (hbody : ∀ i w, NotDone w → Ri i w →
      entails (.cu q φ ψ) (k i) w ∨
        entails (.cu q φ (.ret fun (lr : I ⊕ X) w' =>
          ∃ i', lr = .inl i' ∧ NotDone w' ∧ Ri i' w' ∧ f i' w' < f i w)) (k i) w) :
    entails (.cu q φ ψ) (CTree.iter k i) w :=
  u_iter_prefix Ri (InvImage (· < ·) fun p => f p.1 p.2) (InvImage.wf _ Nat.lt_wfRel.wf) hd hR
    hbody

/-! ## Return-driven iteration -/

/-- Return-driven iteration: continuing returns decrease the rank, while exiting returns
establish the indexed target at the output tree's result type. -/
theorem u_iter {q : Ticlq} (Inv : I → World E → Prop) (Rv : I × World E → I × World E → Prop)
    {i : I} {w : World E} {k : I → CTree E B (I ⊕ X)} {φ : TiclL E} {ψ : Ticl E o}
    (hwf : WellFounded Rv) (hinv : Inv i w)
    (hbody : ∀ s w, Inv s w →
      entails (.cu q φ (.ret fun (lr : I ⊕ X) w' => match lr with
        | .inl s' => Inv s' w' ∧ Rv (s', w') (s, w)
        | .inr r => entails ψ (pure r : CTree E B X) w')) (k s) w) :
    entails (.cu q φ ψ) (CTree.iter k i) w := by
  refine hwf.induction (C := fun p => Inv p.1 p.2 → entails (.cu q φ ψ) (CTree.iter k p.1) p.2)
    (i, w) ?_ hinv
  rintro ⟨s, z⟩ ih hinv
  rw [unfold_iter]
  refine u_bind_r (hbody s z hinv) fun lr w' h => ?_
  cases lr with
  | inl s' => exact (proper_entails_meq _ (sb_guard _)).2 (ih (s', w') h.2 h.1)
  | inr r =>
    cases q
    · exact Auc.matchA h
    · exact Euc.matchE h

/-- Natural-valued ranks for the return-driven algorithm. -/
theorem u_iter_nat {q : Ticlq} (Inv : I → World E → Prop) (f : I → World E → Nat) {i : I}
    {w : World E} {k : I → CTree E B (I ⊕ X)} {φ : TiclL E} {ψ : Ticl E o} (hinv : Inv i w)
    (hbody : ∀ s w, Inv s w →
      entails (.cu q φ (.ret fun (lr : I ⊕ X) w' => match lr with
        | .inl s' => Inv s' w' ∧ f s' w' < f s w
        | .inr r => entails ψ (pure r : CTree E B X) w')) (k s) w) :
    entails (.cu q φ ψ) (CTree.iter k i) w :=
  u_iter Inv (InvImage (· < ·) fun p => f p.1 p.2) (InvImage.wf _ Nat.lt_wfRel.wf) hinv hbody

/-! ## Loop invariants for `AG` and `EG` -/

/-- A loop `iter k i` satisfies `AG φ` if `φ` holds at every loop head and each body `k i` makes
real progress, then satisfies `φ` until it returns `inl i'` with the invariant `R` restored. -/
theorem ag_iter (R : I → World E → Prop) {i : I} {w : World E} {k : I → CTree E B (I ⊕ X)}
    {φ : TiclL E} (hR : R i w)
    (H : ∀ i w, R i w →
      entails φ (CTree.iter k i) w ∧
        entails (AX (φ AU .ret fun (lr : I ⊕ X) w' => ∃ i', lr = .inl i' ∧ R i' w')) (k i) w) :
    entails (AG φ) (CTree.iter k i) w := by
  have hP : SbProper (entails (X := X) (B := B) φ) := fun _ h => proper_entails_meq φ h
  revert i w hR
  coinduction RR hRR CIH
  intro i w hR
  obtain ⟨hφ, -, ⟨k', wk, tr⟩, hn⟩ := H i w hR
  refine ⟨hφ, ?_, fun t' w' htr => ?_⟩
  · rw [unfold_iter]
    exact can_step_bind_l tr (ticl_not_done _ (hn _ _ tr))
  · rw [unfold_iter] at htr
    rcases ktrans_bind_inv htr with ⟨t₀, tr₀, -, rfl⟩ | ⟨y, w₀, tr₀, -, -⟩
    · refine ag_bind_chain hRR (hn _ _ tr₀) fun lr z ⟨j, hlr, hj⟩ => ?_
      subst hlr
      exact (agc_chain_proper (P := entails φ) (fun _ _ _ h => hP _ h) RR hRR _ _ _
        (sb_guard _)).2 (CIH hj)
    · obtain ⟨_, _, -, hs, -⟩ := (au_stuck (φ := φ)).2 (hn _ _ tr₀)
      exact (can_step_stuck hs).elim

/-- A loop `iter k i` satisfies `EG φ` if `φ` holds at every loop head and some run of each body
`k i` makes real progress, then satisfies `φ` until it returns `inl i'` with `R` restored. -/
theorem eg_iter (R : I → World E → Prop) {i : I} {w : World E} {k : I → CTree E B (I ⊕ X)}
    {φ : TiclL E} (hR : R i w)
    (H : ∀ i w, R i w →
      entails φ (CTree.iter k i) w ∧
        entails (EX (φ EU .ret fun (lr : I ⊕ X) w' => ∃ i', lr = .inl i' ∧ R i' w')) (k i) w) :
    entails (EG φ) (CTree.iter k i) w := by
  have hP : SbProper (entails (X := X) (B := B) φ) := fun _ h => proper_entails_meq φ h
  revert i w hR
  coinduction RR hRR CIH
  intro i w hR
  obtain ⟨hφ, -, k', wk, tr, hn⟩ := H i w hR
  change enc _ RR (CTree.iter k i) w
  rw [unfold_iter] at hφ ⊢
  refine ⟨hφ, _, wk, ktrans_bind_l tr (ticl_not_done _ hn),
    eg_bind_chain hRR hn fun lr z ⟨j, hlr, hj⟩ => ?_⟩
  subst hlr
  exact (egc_chain_proper (P := entails φ) (fun _ _ _ h => hP _ h) RR hRR _ _ _
    (sb_guard _)).2 (CIH hj)

end IterLemmas

-- Not ported: nothing. The Rocq-local tower helpers `auc_family_chain`/`euc_family_chain` are
-- private (proved by induction on the until: chain elements are pre-fixpoints).

end Tisl
