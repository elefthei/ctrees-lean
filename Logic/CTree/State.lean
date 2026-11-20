/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Iter
public import Logic.CTree.Trace
public import Logic.Congruence
public import Logic.Interp.State

/-!
# State rules

Modal rules for programs interpreted with a stateful instrumented handler
`h : (e : E.I) → StateT S (ctreeW W B) (E.O e)`: bind, branch, iteration (well-founded, ghost-ranked
and natural-number ranks, `AG`/`EG` invariants) and the `get`/`put` rules of `instr_stateE`
(← `CTree/Logic/State.v`). Lean's `StateT` returns `(value, state)`, so every Rocq pair `(σ, x)`
is `(x, σ)` here; Rocq `relation (I * Σ * WorldW W)` is a relation on `I × S × World (writerE W)`.
-/

@[expose] public section
namespace Tisl
open CTree Coinduction Notation
open ITree (Effect)

section StateLemmas
variable {E B : Effect.{u}} {S W : Type u} (h : (e : E.I) → StateT S (ctreeW W B) (E.O e))
  {σ : S} {o : Option (Type u)}

/-! ## Bind and branches -/

/-- Lift `ticll_bind_l` to state interpretations. -/
theorem ticll_state_bind_l {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {φ : TiclL (writerE W)} {w : World (writerE W)} (H : entails φ (interp_state h t σ) w) :
    entails φ (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact ticll_bind_l H

/-- An interpreted return satisfies a return postcondition. -/
theorem axr_state_ret {X : Type u} {R : X × S → World (writerE W) → Prop} {x : X}
    {w : World (writerE W)} (hR : R (x, σ) w) (hd : NotDone w) :
    entails (.ret R) (interp_state h (pure x : CTree E B X) σ) w := by
  rw [interp_state_ret]; exact ret_ret hd hR

/-- An indexed endpoint establishes `AU` at an interpreted return. -/
theorem au_state_ret {X : Type u} {x : X} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    {w : World (writerE W)} (H : entails ψ (pure (x, σ) : ctreeW W B (X × S)) w) :
    entails (φ AU ψ) (interp_state h (pure x : CTree E B X) σ) w := by
  rw [interp_state_ret]; exact Auc.matchA H

/-- Stateful bind through a return postcondition `R y s`. -/
theorem ticl_state_bind_ret {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {p : Ticl (writerE W) o} {R : Y → S → World (writerE W) → Prop}
    (H : entails (.ret fun (r : Y × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ y s w', R y s w' → entails p (interp_state h (k y) s) w') :
    entails p (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact ticl_bind_ret H fun r w' hr => hk r.1 r.2 w' hr

/-- Stateful bind through a deterministic return `(r, σ')` in `w'`. -/
theorem ticl_state_bind_ret_eq {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {p : Ticl (writerE W) o} {r : Y} {σ' : S} {w' : World (writerE W)}
    (H : entails (ret= (r, σ') w') (interp_state h t σ) w)
    (hk : entails p (interp_state h (k r) σ') w') :
    entails p (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact ticl_bind_ret_eq H hk

/-- Bind lemma for suffix `AN`. -/
theorem an_state_bind_r {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    {R : Y → S → World (writerE W) → Prop}
    (H : entails (.ret fun (r : Y × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ x s w', R x s w' → entails (φ AN ψ) (interp_state h (k x) s) w') :
    entails (φ AN ψ) (interp_state h (t >>= k) σ) w :=
  ticl_state_bind_ret h H hk

/-- Bind lemma for prefix `AN`. -/
theorem an_state_bind_l {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    {R : Y → S → World (writerE W) → Prop}
    (H : entails (φ AN .ret fun (r : Y × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ x s w', R x s w' → entails ψ (interp_state h (k x) s) w') :
    entails (φ AN ψ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact an_bind_l H fun r w' hr => hk r.1 r.2 w' hr

/-- Deterministic-prefix variant of `an_state_bind_r`. -/
theorem an_state_bind_r_eq {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w w' : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o} {r : Y}
    {σ' : S} (H : entails (ret= (r, σ') w') (interp_state h t σ) w)
    (hk : entails (φ AN ψ) (interp_state h (k r) σ') w') :
    entails (φ AN ψ) (interp_state h (t >>= k) σ) w :=
  ticl_state_bind_ret_eq h H hk

/-- Deterministic-prefix variant of `an_state_bind_l`. -/
theorem an_state_bind_l_eq {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w w' : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o} {r : Y}
    {σ' : S} (H : entails (φ AN ret= (r, σ') w') (interp_state h t σ) w)
    (hk : entails ψ (interp_state h (k r) σ') w') :
    entails (φ AN ψ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]
  exact an_bind_l H (by rintro _ _ ⟨rfl, rfl⟩; exact hk)

/-- Bind lemma for suffix `EN`. -/
theorem en_state_bind_r {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    {R : Y → S → World (writerE W) → Prop}
    (H : entails (.ret fun (r : Y × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ x s w', R x s w' → entails (φ EN ψ) (interp_state h (k x) s) w') :
    entails (φ EN ψ) (interp_state h (t >>= k) σ) w :=
  ticl_state_bind_ret h H hk

/-- Deterministic-prefix variant of `en_state_bind_r`. -/
theorem en_state_bind_r_eq {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w w' : World (writerE W)} {r : Y} {σ' : S} {φ : TiclL (writerE W)}
    {ψ : Ticl (writerE W) o} (H : entails (ret= (r, σ') w') (interp_state h t σ) w)
    (hk : entails (φ EN ψ) (interp_state h (k r) σ') w') :
    entails (φ EN ψ) (interp_state h (t >>= k) σ) w :=
  ticl_state_bind_ret_eq h H hk

/-- Visible branches under `interp_state` for suffix `AN`. -/
theorem an_state_brS {X : Type u} {c : B.I} {k : B.O c → CTree E B X} (y : B.O c)
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o} :
    entails (φ AN ψ) (interp_state h (CTree.brS c k) σ) w ↔
      entails φ (interp_state h (CTree.brS c k) σ) w ∧
        ∀ y, entails ψ (interp_state h (k y) σ) w := by
  rw [proper_entails_meq (φ AN ψ) (interp_state_brS h c k σ),
    proper_entails_meq φ (interp_state_brS h c k σ)]
  exact an_brS y

/-- Hidden branches under `interp_state` for suffix `AN`: all successors of all interpreted
branches satisfy `ψ`, and at least one branch can step. -/
theorem an_state_br {X : Type u} {c : B.I} {k : B.O c → CTree E B X} {w : World (writerE W)}
    {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    (Hφ : entails φ (interp_state h (CTree.br c k) σ) w)
    (Hs : ∃ y, can_step (interp_state h (k y) σ) w)
    (Hk : ∀ y t' w', ktrans (interp_state h (k y) σ) w t' w' → entails ψ t' w') :
    entails (φ AN ψ) (interp_state h (CTree.br c k) σ) w := by
  simp only [interp_state_br, bind_branch'] at Hφ ⊢
  refine an_br Hφ ?_ fun y t' w' tr => Hk y t' w' (ktrans_guard.1 tr)
  obtain ⟨y, hs⟩ := Hs
  exact ⟨y, can_step_guard.2 hs⟩

/-- Bind lemma for suffix `AU`. -/
theorem au_state_bind_r {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    {R : Y → S → World (writerE W) → Prop}
    (H : entails (φ AU .ret fun (r : Y × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ x s w', R x s w' → entails (φ AU ψ) (interp_state h (k x) s) w') :
    entails (φ AU ψ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact u_bind_r H fun r w' hr => hk r.1 r.2 w' hr

/-- Deterministic-prefix variant of `au_state_bind_r`. -/
theorem au_state_bind_r_eq {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o} {x' : Y} {σ' : S}
    {w' : World (writerE W)} (H : entails (φ AU ret= (x', σ') w') (interp_state h t σ) w)
    (hk : entails (φ AU ψ) (interp_state h (k x') σ') w') :
    entails (φ AU ψ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact u_bind_r_eq H hk

/-- Bind lemma for suffix `EU`. -/
theorem eu_state_bind_r {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    {R : Y → S → World (writerE W) → Prop}
    (H : entails (φ EU .ret fun (r : Y × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ r s w', R r s w' → entails (φ EU ψ) (interp_state h (k r) s) w') :
    entails (φ EU ψ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact u_bind_r H fun r w' hr => hk r.1 r.2 w' hr

/-- Deterministic-prefix variant of `eu_state_bind_r`. -/
theorem eu_state_bind_r_eq {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o} {x' : Y} {σ' : S}
    {w' : World (writerE W)} (H : entails (φ EU ret= (x', σ') w') (interp_state h t σ) w)
    (hk : entails (φ EU ψ) (interp_state h (k x') σ') w') :
    entails (φ EU ψ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact u_bind_r_eq H hk

/-- Bind lemma for `AG`: a finite prefix `t` reaches a return, then `AG` holds on the
continuation. -/
theorem ag_state_bind_r {X Y : Type u} {t : CTree E B X} {w : World (writerE W)}
    {k : X → CTree E B Y} {φ : TiclL (writerE W)} {R : X → S → World (writerE W) → Prop}
    (H : entails (φ AU .ret fun (r : X × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ x s w', R x s w' → entails (AG φ) (interp_state h (k x) s) w') :
    entails (AG φ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact ag_bind_r H fun r w' hr => hk r.1 r.2 w' hr

/-- Deterministic-prefix variant of `ag_state_bind_r`. -/
theorem ag_state_bind_r_eq {X Y : Type u} {t : CTree E B X} {w w' : World (writerE W)}
    {k : X → CTree E B Y} {φ : TiclL (writerE W)} {x' : X} {σ' : S}
    (H : entails (φ AU ret= (x', σ') w') (interp_state h t σ) w)
    (hk : entails (AG φ) (interp_state h (k x') σ') w') :
    entails (AG φ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]
  exact ag_bind_r H (by rintro _ _ ⟨rfl, rfl⟩; exact hk)

/-- Bind lemma for `EG`. -/
theorem eg_state_bind_r {X Y : Type u} {t : CTree E B X} {w : World (writerE W)}
    {k : X → CTree E B Y} {R : X → S → World (writerE W) → Prop} {φ : TiclL (writerE W)}
    (H : entails (φ EU .ret fun (r : X × S) => R r.1 r.2) (interp_state h t σ) w)
    (hk : ∀ r s w', R r s w' → entails (EG φ) (interp_state h (k r) s) w') :
    entails (EG φ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact eg_bind_r H fun r w' hr => hk r.1 r.2 w' hr

/-- Deterministic-prefix variant of `eg_state_bind_r`. -/
theorem eg_state_bind_r_eq {X Y : Type u} {t : CTree E B X} {w w' : World (writerE W)}
    {k : X → CTree E B Y} {φ : TiclL (writerE W)} {x' : X} {σ' : S}
    (H : entails (φ EU ret= (x', σ') w') (interp_state h t σ) w)
    (hk : entails (EG φ) (interp_state h (k x') σ') w') :
    entails (EG φ) (interp_state h (t >>= k) σ) w := by
  rw [interp_state_bind]; exact eg_bind_r_eq H hk

/-! ## Iteration -/

/-- Monotonicity of the return postcondition under an until. -/
private theorem u_ret_mono {X : Type u} {q : Ticlq} {t : ctreeW W B X} {w : World (writerE W)}
    {φ : TiclL (writerE W)} {P Q : X → World (writerE W) → Prop} (hPQ : ∀ x w, P x w → Q x w)
    (H : entails (.cu q φ (.ret P)) t w) : entails (.cu q φ (.ret Q)) t w :=
  impl_ticl_until q (impl_ticl_refl φ) (ret_impl_ticl P Q hPQ) t w H

/-- Prefix iteration for either next quantifier (lifts `n_iter_prefix`). -/
theorem n_state_iter_prefix {X I : Type u} {q : Ticlq} (Ri : I → S → World (writerE W) → Prop)
    (Rv : I → I → Prop) {i : I} {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)}
    {φ ψ : TiclL (writerE W)} (hwf : WellFounded Rv) (hi : Ri i σ w)
    (H : ∀ i s w, Ri i s w →
      entails (.cx q φ ψ) (interp_state h (k i) s) w ∨
        entails (.ret fun (p : (I ⊕ X) × S) w' => ∃ i', p.1 = .inl i' ∧ Ri i' p.2 w' ∧ Rv i' i)
          (interp_state h (k i) s) w) :
    entails (.cx q φ ψ) (interp_state h (CTree.iter k i) σ) w := by
  induction i using hwf.induction generalizing σ w with
  | _ i ih =>
  rw [interp_state_unfold_iter]
  rcases H i σ w hi with H' | H'
  · exact ticll_bind_l H'
  · refine ticl_bind_ret H' fun ⟨lr, s'⟩ w' ⟨j, hlr, hj, hv⟩ => ?_
    obtain rfl : lr = .inl j := hlr
    exact (proper_entails_meq _ (sb_guard _)).2 (ih j hv hj)

/-- `n_state_iter_prefix` at `AN`. -/
theorem anl_state_iter {X I : Type u} (Ri : I → S → World (writerE W) → Prop) (Rv : I → I → Prop)
    {i : I} {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)}
    (hwf : WellFounded Rv) (hi : Ri i σ w)
    (H : ∀ i s w, Ri i s w →
      entails (φ AN ψ) (interp_state h (k i) s) w ∨
        entails (.ret fun (p : (I ⊕ X) × S) w' => ∃ i', p.1 = .inl i' ∧ Ri i' p.2 w' ∧ Rv i' i)
          (interp_state h (k i) s) w) :
    entails (φ AN ψ) (interp_state h (CTree.iter k i) σ) w :=
  n_state_iter_prefix h Ri Rv hwf hi H

/-- `n_state_iter_prefix` at `EN`. -/
theorem enl_state_iter {X I : Type u} (Ri : I → S → World (writerE W) → Prop) (Rv : I → I → Prop)
    {i : I} {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)}
    (hwf : WellFounded Rv) (hi : Ri i σ w)
    (H : ∀ i s w, Ri i s w →
      entails (φ EN ψ) (interp_state h (k i) s) w ∨
        entails (.ret fun (p : (I ⊕ X) × S) w' => ∃ i', p.1 = .inl i' ∧ Ri i' p.2 w' ∧ Rv i' i)
          (interp_state h (k i) s) w) :
    entails (φ EN ψ) (interp_state h (CTree.iter k i) σ) w :=
  n_state_iter_prefix h Ri Rv hwf hi H

/-- Ghost-ranked direct-prefix iteration: the rank `g` may relate control, concrete state and
observation world without being determined by them; the body may establish the endpoint before
returning. -/
theorem u_state_iter_prefix_ghost {X I : Type u} {G : Type v} {q : Ticlq}
    (Ri : G → I → S → World (writerE W) → Prop) (ltG : G → G → Prop)
    {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)} (hwf : WellFounded ltG)
    (H : ∀ g i s w, NotDone w → Ri g i s w →
      entails (.cu q φ ψ) (interp_state h (k i) s) w ∨
        entails (.cu q φ (.ret fun (p : (I ⊕ X) × S) w' =>
            ∃ g' i', p.1 = .inl i' ∧ NotDone w' ∧ Ri g' i' p.2 w' ∧ ltG g' g))
          (interp_state h (k i) s) w) :
    ∀ g i s w, NotDone w → Ri g i s w →
      entails (.cu q φ ψ) (interp_state h (CTree.iter k i) s) w := by
  intro g
  induction g using hwf.induction with
  | _ g ih =>
  intro i s w hd hi
  rw [interp_state_unfold_iter]
  rcases H g i s w hd hi with H' | H'
  · exact ticll_bind_l H'
  · refine u_bind_r H' fun ⟨lr, s'⟩ w' ⟨g', j, hlr, hd', hj, hlt⟩ => ?_
    obtain rfl : lr = .inl j := hlr
    exact (proper_entails_meq _ (sb_guard _)).2 (ih g' hlt j s' w' hd' hj)

/-- Ghost-ranked return-driven iteration: a decreasing loop-head return or a final return
satisfying an arbitrary indexed endpoint. -/
theorem u_state_iter_ghost {X I : Type u} {G : Type v} {q : Ticlq}
    (Ri : G → I → S → World (writerE W) → Prop) (ltG : G → G → Prop)
    {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    (hwf : WellFounded ltG)
    (H : ∀ g i s w, NotDone w → Ri g i s w →
      entails (.cu q φ (.ret fun (p : (I ⊕ X) × S) w' => match p with
          | (.inl i', s') => ∃ g', NotDone w' ∧ Ri g' i' s' w' ∧ ltG g' g
          | (.inr x, s') => entails ψ (pure (x, s') : ctreeW W B (X × S)) w'))
        (interp_state h (k i) s) w) :
    ∀ g i s w, NotDone w → Ri g i s w →
      entails (.cu q φ ψ) (interp_state h (CTree.iter k i) s) w := by
  intro g
  induction g using hwf.induction with
  | _ g ih =>
  intro i s w hd hi
  rw [interp_state_unfold_iter]
  refine u_bind_r (H g i s w hd hi) fun ⟨lr, s'⟩ w' hr => ?_
  cases lr with
  | inl j =>
    obtain ⟨g', hd', hj, hlt⟩ := hr
    exact (proper_entails_meq _ (sb_guard _)).2 (ih g' hlt j s' w' hd' hj)
  | inr x =>
    cases q
    · exact Auc.matchA hr
    · exact Euc.matchE hr

/-- Direct-body prefix iteration for either until quantifier, ranked on `I × S × World`. -/
theorem u_state_iter_prefix {X I : Type u} {q : Ticlq} (Ri : I → S → World (writerE W) → Prop)
    (Rv : I × S × World (writerE W) → I × S × World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)}
    (hwf : WellFounded Rv) (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (.cu q φ ψ) (interp_state h (k i) s) w ∨
        entails (.cu q φ (.ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w' ∧ Rv (i', p.2, w') (i, s, w)))
          (interp_state h (k i) s) w) :
    entails (.cu q φ ψ) (interp_state h (CTree.iter k i) σ) w := by
  refine u_state_iter_prefix_ghost h (fun g i s z => g = (i, s, z) ∧ Ri i s z) Rv hwf ?_
    (i, σ, w) i σ w hd ⟨rfl, hi⟩
  rintro _ i s w hd ⟨rfl, hi⟩
  refine (H i s w hd hi).imp id (u_ret_mono ?_)
  rintro ⟨lr, s'⟩ w' ⟨j, hlr, hd', hj, hv⟩
  exact ⟨(j, s', w'), j, hlr, hd', ⟨rfl, hj⟩, hv⟩

/-- `u_state_iter_prefix` at `AU`. -/
theorem au_state_iter_prefix {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (Rv : I × S × World (writerE W) → I × S × World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)}
    (hwf : WellFounded Rv) (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ AU ψ) (interp_state h (k i) s) w ∨
        entails (φ AU .ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w' ∧ Rv (i', p.2, w') (i, s, w))
          (interp_state h (k i) s) w) :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter_prefix h Ri Rv hwf hd hi H

/-- `u_state_iter_prefix` at `EU`. -/
theorem eu_state_iter_prefix {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (Rv : I × S × World (writerE W) → I × S × World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)}
    (hwf : WellFounded Rv) (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ EU ψ) (interp_state h (k i) s) w ∨
        entails (φ EU .ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w' ∧ Rv (i', p.2, w') (i, s, w))
          (interp_state h (k i) s) w) :
    entails (φ EU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter_prefix h Ri Rv hwf hd hi H

/-- One unfolding of an `AU` proof whose body returns a continuing state (lifts `u_iter_next`). -/
theorem au_state_iter_next {X I : Type u} (R : I → S → World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)}
    {ψ : Ticl (writerE W) o}
    (H : entails (φ AU .ret fun (p : (I ⊕ X) × S) w =>
        ∃ i, p.1 = .inl i ∧ NotDone w ∧ R i p.2 w) (interp_state h (k i) σ) w)
    (hnext : ∀ i s w, R i s w → NotDone w →
      entails (φ AU ψ) (interp_state h (CTree.iter k i) s) w) :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w := by
  rw [interp_state_unfold_iter]
  refine u_bind_r H fun ⟨lr, s'⟩ w' ⟨j, hlr, hd, hj⟩ => ?_
  obtain rfl : lr = .inl j := hlr
  exact (proper_entails_meq _ (sb_guard _)).2 (hnext j s' w' hj hd)

/-- Deterministic variant of `au_state_iter_next`. -/
theorem au_state_iter_next_eq {X I : Type u} {i i' : I} {w w' : World (writerE W)} {σ' : S}
    {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    (H : entails (φ AU ret= ((.inl i' : I ⊕ X), σ') w') (interp_state h (k i) σ) w)
    (_hd : NotDone w') (hk : entails (φ AU ψ) (interp_state h (CTree.iter k i') σ') w') :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w := by
  rw [interp_state_unfold_iter]
  exact u_bind_r_eq H ((proper_entails_meq _ (sb_guard _)).2 hk)

/-- Split liveness between an established region `Ri` and an `Rv`-decreasing continuation
(lifts `u_iter_split`). -/
theorem aul_state_iter_split {X I : Type u} (R Ri : I → S → World (writerE W) → Prop)
    (Rv : I × S × World (writerE W) → I × S × World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)}
    (hwf : WellFounded Rv) (hd : NotDone w) (hR : R i σ w)
    (H : ∀ i s w, NotDone w → R i s w →
      entails (φ AU .ret fun (p : (I ⊕ X) × S) w' =>
          ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w') (interp_state h (k i) s) w ∨
        entails (φ AU .ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ R i' p.2 w' ∧ Rv (i', p.2, w') (i, s, w))
          (interp_state h (k i) s) w)
    (Hi : ∀ i w s, NotDone w → Ri i s w →
      entails (φ AU ψ) (interp_state h (CTree.iter k i) s) w) :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w := by
  refine hwf.induction (C := fun p => NotDone p.2.2 → R p.1 p.2.1 p.2.2 →
    entails (φ AU ψ) (interp_state h (CTree.iter k p.1) p.2.1) p.2.2) (i, σ, w) ?_ hd hR
  rintro ⟨i, s, w⟩ ih hd hR
  rcases H i s w hd hR with H' | H'
  · exact au_state_iter_next h Ri H' fun j s' w' hj hd' => Hi j w' s' hd' hj
  · exact au_state_iter_next h (fun j s' w' => R j s' w' ∧ Rv (j, s', w') (i, s, w)) H'
      fun j s' w' ⟨hj, hv⟩ hd' => ih (j, s', w') hv hd' hj

/-- Return-driven iteration for either until quantifier: continuing returns decrease `Rv`,
exiting returns establish the indexed target. -/
theorem u_state_iter {X I : Type u} {q : Ticlq} (Ri : I → S → World (writerE W) → Prop)
    (Rv : I × S × World (writerE W) → I × S × World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)}
    {ψ : Ticl (writerE W) o} (hwf : WellFounded Rv) (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (.cu q φ (.ret fun (p : (I ⊕ X) × S) w' => match p with
          | (.inl i', s') => NotDone w' ∧ Ri i' s' w' ∧ Rv (i', s', w') (i, s, w)
          | (.inr r, s') => entails ψ (pure (r, s') : ctreeW W B (X × S)) w'))
        (interp_state h (k i) s) w) :
    entails (.cu q φ ψ) (interp_state h (CTree.iter k i) σ) w := by
  refine u_state_iter_ghost h (fun g i s z => g = (i, s, z) ∧ Ri i s z) Rv hwf ?_
    (i, σ, w) i σ w hd ⟨rfl, hi⟩
  rintro _ i s w hd ⟨rfl, hi⟩
  refine u_ret_mono ?_ (H i s w hd hi)
  rintro ⟨lr | r, s'⟩ w' hr
  · exact ⟨(lr, s', w'), hr.1, ⟨rfl, hr.2.1⟩, hr.2.2⟩
  · exact hr

/-- `u_state_iter` at `AU`. -/
theorem au_state_iter {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (Rv : I × S × World (writerE W) → I × S × World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)}
    {ψ : Ticl (writerE W) o} (hwf : WellFounded Rv) (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ AU .ret fun (p : (I ⊕ X) × S) w' => match p with
          | (.inl i', s') => NotDone w' ∧ Ri i' s' w' ∧ Rv (i', s', w') (i, s, w)
          | (.inr r, s') => entails ψ (pure (r, s') : ctreeW W B (X × S)) w')
        (interp_state h (k i) s) w) :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter h Ri Rv hwf hd hi H

/-- `u_state_iter` at `EU`. -/
theorem eu_state_iter {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (Rv : I × S × World (writerE W) → I × S × World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)}
    {ψ : Ticl (writerE W) o} (hwf : WellFounded Rv) (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ EU .ret fun (p : (I ⊕ X) × S) w' => match p with
          | (.inl i', s') => NotDone w' ∧ Ri i' s' w' ∧ Rv (i', s', w') (i, s, w)
          | (.inr r, s') => entails ψ (pure (r, s') : ctreeW W B (X × S)) w')
        (interp_state h (k i) s) w) :
    entails (φ EU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter h Ri Rv hwf hd hi H

/-- Loop invariant for `AG` (lifts `ag_iter`): `φ` holds at every loop head and each body makes
real progress, then satisfies `φ` until it returns `inl i'` with `R` restored. -/
theorem ag_state_iter {X I : Type u} (R : I → S → World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)}
    (hd : NotDone w) (hR : R i σ w)
    (H : ∀ i s w, NotDone w → R i s w →
      entails φ (interp_state h (CTree.iter k i) s) w ∧
        entails (AX (φ AU .ret fun (p : (I ⊕ X) × S) w' =>
          ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ R i' p.2 w')) (interp_state h (k i) s) w) :
    entails (AG φ) (interp_state h (CTree.iter k i) σ) w := by
  have hP : SbProper (entails (X := X × S) (B := B) φ) := fun _ h => proper_entails_meq φ h
  refine coinduction (b := agcF (entails φ))
    (fun p : (Σ' i s w, NotDone w ∧ R i s w) => interp_state h (CTree.iter k p.1) p.2.1)
    (fun p => p.2.2.1) (fun RR hRR CIH => ?_) ⟨i, σ, w, hd, hR⟩
  rintro ⟨i, s, w, hd, hR⟩
  obtain ⟨hφ, -, ⟨k', wk, tr⟩, hn⟩ := H i s w hd hR
  refine ⟨hφ, ?_, fun t' w' htr => ?_⟩
  · rw [interp_state_unfold_iter]
    exact can_step_bind_l tr (ticl_not_done _ (hn _ _ tr))
  · rw [interp_state_unfold_iter] at htr
    rcases ktrans_bind_inv htr with ⟨t₀, tr₀, -, rfl⟩ | ⟨y, w₀, tr₀, -, -⟩
    · refine ag_bind_chain hRR (hn _ _ tr₀) fun ⟨lr, s'⟩ z ⟨j, hlr, hd', hj⟩ => ?_
      obtain rfl : lr = .inl j := hlr
      exact (agc_chain_proper (P := entails φ) (fun _ _ _ h => hP _ h) RR hRR _ _ _
        (sb_guard _)).2 (CIH ⟨j, s', z, hd', hj⟩)
    · obtain ⟨_, _, -, hs, -⟩ := (au_stuck (φ := φ)).2 (hn _ _ tr₀)
      exact (can_step_stuck hs).elim

/-- Continuation-aware invariance: when every body run is a nonempty finite log prefix returning
to the invariant, `AG φ` holds provided `φ` is preserved by logs and holds at loop heads. Pending
observations keep the actual next iteration rather than a detached body ending in `pure`. -/
theorem ag_state_iter_logs {X I : Type u} (Inv : I → S → Prop) {k : I → CTree E B (I ⊕ X)}
    {φ : TiclL (writerE W)}
    (Hbody : ∀ i s, Inv i s → ∃ i' s' logs, logs ≠ [] ∧
      interp_state h (k i) s ~ emit_list (B := B) logs (pure ((.inl i' : I ⊕ X), s')) ∧ Inv i' s')
    (Hlog : ∀ (o : W) (t : ctreeW W B (X × S)) w, NotDone w →
      entails φ t (.obs (E := writerE W) o ⟨⟩) →
      entails φ (CTree.vis (E := writerE W) o fun _ => t) w)
    (Hboundary : ∀ i s w, Inv i s → NotDone w →
      entails φ (interp_state h (CTree.iter k i) s) w) :
    ∀ i s w, Inv i s → NotDone w → entails (AG φ) (interp_state h (CTree.iter k i) s) w := by
  have hP : SbProper (entails (X := X × S) (B := B) φ) := fun _ h => proper_entails_meq φ h
  have Hloop : ∀ i s, Inv i s → ∃ i' s' logs, logs ≠ [] ∧
      interp_state h (CTree.iter k i) s ~
        emit_list logs (interp_state h (CTree.iter k i') s') ∧ Inv i' s' := by
    intro i s hinv
    obtain ⟨i', s', logs, hne, hrun, hinv'⟩ := Hbody i s hinv
    refine ⟨i', s', logs, hne, ?_, hinv'⟩
    rw [interp_state_unfold_iter]
    refine sbisim_trans (sbisim_clo_bind_eq hrun fun _ => sbisim_refl _) ?_
    rw [emit_list_ret_bind]
    exact emit_list_sbisim _ (sb_guard _)
  have Hpref : ∀ (pending : List W) i s w, Inv i s → NotDone w →
      entails φ (emit_list pending (interp_state h (CTree.iter k i) s)) w := by
    intro pending
    induction pending with
    | nil => exact Hboundary
    | cons o rest ih =>
      intro i s w hinv hw
      rw [emit_list_cons]
      exact Hlog o _ w hw (ih i s _ hinv (.obs _ _))
  have Hsuffix := coinduction (b := agcF (entails φ))
    (fun p : (Σ' (i : I) (s : S) (pending : List W) (w : World (writerE W)), Inv i s ∧ NotDone w)
      => emit_list p.2.2.1 (interp_state h (CTree.iter k p.1) p.2.1))
    (fun p => p.2.2.2.1) ?_
  · intro i s w hinv hw
    exact Hsuffix ⟨i, s, [], w, hinv, hw⟩
  intro RR hRR CIH
  rintro ⟨i, s, pending, w, hinv, hw⟩
  have Hfront : ∃ j s' o rest, Inv j s' ∧
      emit_list pending (interp_state h (CTree.iter k i) s) ~
        CTree.vis (E := writerE W) o fun _ =>
          emit_list rest (interp_state h (CTree.iter k j) s') := by
    cases pending with
    | nil =>
      obtain ⟨j, s', logs, hne, hrun, hj⟩ := Hloop i s hinv
      cases logs with
      | nil => exact (hne rfl).elim
      | cons o rest => rw [emit_list_cons] at hrun; exact ⟨j, s', o, rest, hj, hrun⟩
    | cons o rest => exact ⟨i, s, o, rest, hinv, by rw [emit_list_cons]; exact sbisim_refl _⟩
  obtain ⟨j, s', o, rest, hj, hfront⟩ := Hfront
  have hRp := agc_chain_proper (P := entails φ) (fun _ _ _ h => hP _ h) RR hRR
  refine (proper_ax_equ (P := entails φ) (Q := RR) (fun _ _ _ h => hP _ h) hRp hfront).2 ?_
  refine ⟨Hlog o _ w hw (Hpref rest j s' _ hj (.obs _ _)), (can_step_vis PUnit.unit).2 hw,
    fun t' w' tr => ?_⟩
  obtain ⟨_, rfl, rfl, -⟩ := ktrans_vis.1 tr
  exact CIH ⟨j, s', rest, _, hj, .obs _ _⟩

/-- Loop invariant for `EG` (lifts `eg_iter`). -/
theorem eg_state_iter {X I : Type u} (R : I → S → World (writerE W) → Prop) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)}
    (hR : R i σ w) (hd : NotDone w)
    (H : ∀ i s w, NotDone w → R i s w →
      entails φ (interp_state h (CTree.iter k i) s) w ∧
        entails (EX (φ EU .ret fun (p : (I ⊕ X) × S) w' =>
          ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ R i' p.2 w')) (interp_state h (k i) s) w) :
    entails (EG φ) (interp_state h (CTree.iter k i) σ) w := by
  have hP : SbProper (entails (X := X × S) (B := B) φ) := fun _ h => proper_entails_meq φ h
  refine coinduction (b := egcF (entails φ))
    (fun p : (Σ' i s w, NotDone w ∧ R i s w) => interp_state h (CTree.iter k p.1) p.2.1)
    (fun p => p.2.2.1) (fun RR hRR CIH => ?_) ⟨i, σ, w, hd, hR⟩
  rintro ⟨i, s, w, hd, hR⟩
  obtain ⟨hφ, -, k', wk, tr, hn⟩ := H i s w hd hR
  change enc _ RR (interp_state h (CTree.iter k i) s) w
  rw [interp_state_unfold_iter] at hφ ⊢
  refine ⟨hφ, _, wk, ktrans_bind_l tr (ticl_not_done _ hn),
    eg_bind_chain hRR hn fun ⟨lr, s'⟩ z ⟨j, hlr, hd', hj⟩ => ?_⟩
  obtain rfl : lr = .inl j := hlr
  exact (egc_chain_proper (P := entails φ) (fun _ _ _ h => hP _ h) RR hRR _ _ _
    (sb_guard _)).2 (CIH ⟨j, s', z, hd', hj⟩)

/-! ## Natural-number ranks -/

/-- `u_state_iter_prefix` with a natural-number rank `f`. -/
theorem u_state_iter_prefix_nat {X I : Type u} {q : Ticlq}
    (Ri : I → S → World (writerE W) → Prop) (f : I → S → World (writerE W) → Nat) {i : I}
    {w : World (writerE W)} {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)}
    (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (.cu q φ ψ) (interp_state h (k i) s) w ∨
        entails (.cu q φ (.ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w' ∧ f i' p.2 w' < f i s w))
          (interp_state h (k i) s) w) :
    entails (.cu q φ ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter_prefix h Ri (InvImage (· < ·) fun p => f p.1 p.2.1 p.2.2)
    (InvImage.wf _ Nat.lt_wfRel.wf) hd hi H

/-- `u_state_iter_prefix_nat` at `AU`. -/
theorem au_state_iter_prefix_nat {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (f : I → S → World (writerE W) → Nat) {i : I} {w : World (writerE W)}
    {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)} (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ AU ψ) (interp_state h (k i) s) w ∨
        entails (φ AU .ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w' ∧ f i' p.2 w' < f i s w)
          (interp_state h (k i) s) w) :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter_prefix_nat h Ri f hd hi H

/-- `aul_state_iter_split` with a natural-number rank `f`. -/
theorem aul_state_iter_split_nat {X I : Type u} (R Ri : I → S → World (writerE W) → Prop)
    (f : I → S → World (writerE W) → Nat) {i : I} {w : World (writerE W)}
    {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)} (hd : NotDone w) (hR : R i σ w)
    (H : ∀ i s w, NotDone w → R i s w →
      entails (φ AU .ret fun (p : (I ⊕ X) × S) w' =>
          ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w') (interp_state h (k i) s) w ∨
        entails (φ AU .ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ R i' p.2 w' ∧ f i' p.2 w' < f i s w)
          (interp_state h (k i) s) w)
    (Hi : ∀ i w s, NotDone w → Ri i s w →
      entails (φ AU ψ) (interp_state h (CTree.iter k i) s) w) :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w :=
  aul_state_iter_split h R Ri (InvImage (· < ·) fun p => f p.1 p.2.1 p.2.2)
    (InvImage.wf _ Nat.lt_wfRel.wf) hd hR H Hi

/-- `u_state_iter` with a natural-number rank `f`. -/
theorem u_state_iter_nat {X I : Type u} {q : Ticlq} (Ri : I → S → World (writerE W) → Prop)
    (f : I → S → World (writerE W) → Nat) {i : I} {w : World (writerE W)}
    {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (.cu q φ (.ret fun (p : (I ⊕ X) × S) w' => match p with
          | (.inl i', s') => NotDone w' ∧ Ri i' s' w' ∧ f i' s' w' < f i s w
          | (.inr r, s') => entails ψ (pure (r, s') : ctreeW W B (X × S)) w'))
        (interp_state h (k i) s) w) :
    entails (.cu q φ ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter h Ri (InvImage (· < ·) fun p => f p.1 p.2.1 p.2.2)
    (InvImage.wf _ Nat.lt_wfRel.wf) hd hi H

/-- `u_state_iter_nat` at `AU`. -/
theorem au_state_iter_nat {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (f : I → S → World (writerE W) → Nat) {i : I} {w : World (writerE W)}
    {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ AU .ret fun (p : (I ⊕ X) × S) w' => match p with
          | (.inl i', s') => NotDone w' ∧ Ri i' s' w' ∧ f i' s' w' < f i s w
          | (.inr r, s') => entails ψ (pure (r, s') : ctreeW W B (X × S)) w')
        (interp_state h (k i) s) w) :
    entails (φ AU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter_nat h Ri f hd hi H

/-- `u_state_iter_prefix_nat` at `EU`. -/
theorem eu_state_iter_prefix_nat {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (f : I → S → World (writerE W) → Nat) {i : I} {w : World (writerE W)}
    {k : I → CTree E B (I ⊕ X)} {φ ψ : TiclL (writerE W)} (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ EU ψ) (interp_state h (k i) s) w ∨
        entails (φ EU .ret fun (p : (I ⊕ X) × S) w' =>
            ∃ i', p.1 = .inl i' ∧ NotDone w' ∧ Ri i' p.2 w' ∧ f i' p.2 w' < f i s w)
          (interp_state h (k i) s) w) :
    entails (φ EU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter_prefix_nat h Ri f hd hi H

/-- `u_state_iter_nat` at `EU`. -/
theorem eu_state_iter_nat {X I : Type u} (Ri : I → S → World (writerE W) → Prop)
    (f : I → S → World (writerE W) → Nat) {i : I} {w : World (writerE W)}
    {k : I → CTree E B (I ⊕ X)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) o}
    (hd : NotDone w) (hi : Ri i σ w)
    (H : ∀ i s w, NotDone w → Ri i s w →
      entails (φ EU .ret fun (p : (I ⊕ X) × S) w' => match p with
          | (.inl i', s') => NotDone w' ∧ Ri i' s' w' ∧ f i' s' w' < f i s w
          | (.inr r, s') => entails ψ (pure (r, s') : ctreeW W B (X × S)) w')
        (interp_state h (k i) s) w) :
    entails (φ EU ψ) (interp_state h (CTree.iter k i) σ) w :=
  u_state_iter_nat h Ri f hd hi H

end StateLemmas

/-! ## `get` and `put` under `instr_stateE` -/

section StateELemmas
variable {B : Effect.{u}} {S : Type u} {s : S} {o : Option (Type u)}

/-- `get` terminates in one step and returns the initial state. -/
theorem axr_get {w : World (writerE S)} {R : S × S → World (writerE S) → Prop}
    (hd : NotDone w) (hR : R (s, s) w) :
    entails (.ret R) (instr_stateE (CTree.get : CTree (stateE S) B S) s) w :=
  (proper_entails_meq _ (interp_state_get s)).2 (ret_ret hd hR)

/-- `get` eventually terminates. -/
theorem aur_get {w : World (writerE S)} {ψ : TiclL (writerE S)}
    {R : S × S → World (writerE S) → Prop} (hd : NotDone w) (hR : R (s, s) w) :
    entails (ψ AU .ret R) (instr_stateE (CTree.get : CTree (stateE S) B S) s) w :=
  Auc.matchA (axr_get hd hR)

/-- `put s'` logs `s'`, then returns `(⟨⟩, s')` satisfying the indexed endpoint. -/
theorem au_put {s' : S} {w : World (writerE S)} {φ : TiclL (writerE S)}
    {ψ : Ticl (writerE S) o} (Hφ : entails φ (log s' : ctreeW S B PUnit) w)
    (Hψ : entails ψ (pure (⟨⟩, s') : ctreeW S B (PUnit × S)) (.obs (E := writerE S) s' ⟨⟩)) :
    entails (φ AU ψ) (instr_stateE (CTree.put s' : CTree (stateE S) B PUnit) s) w :=
  (proper_entails_meq _ (interp_state_put s s')).2 (ticl_an_au (an_log Hψ (ticll_bind_l Hφ)))

/-- `get` terminates on some path. -/
theorem eur_get {w : World (writerE S)} {ψ : TiclL (writerE S)}
    {R : S × S → World (writerE S) → Prop} (hR : R (s, s) w) (hd : NotDone w) :
    entails (ψ EU .ret R) (instr_stateE (CTree.get : CTree (stateE S) B S) s) w :=
  Euc.matchE (axr_get hd hR)

/-- `put s'` logs `s'` then returns `(⟨⟩, s')` on some path. -/
theorem eur_put {s' : S} {w : World (writerE S)} {ψ : TiclL (writerE S)}
    {R : PUnit × S → World (writerE S) → Prop} (Hψ : entails ψ (log s' : ctreeW S B PUnit) w)
    (hR : R (⟨⟩, s') (.obs (E := writerE S) s' ⟨⟩)) :
    entails (ψ EU .ret R) (instr_stateE (CTree.put s' : CTree (stateE S) B PUnit) s) w :=
  (proper_entails_meq _ (interp_state_put s s')).2
    (eu_log (Euc.matchE (ret_ret (.obs _ _) hR)) (ticll_bind_l Hψ))

end StateELemmas

-- Not ported: nothing. `ticllW`/`ticlrW`/`WorldW` notations are written out as
-- `TiclL (writerE W)`, `TiclR (writerE W) X`, `World (writerE W)`.

end Tisl
