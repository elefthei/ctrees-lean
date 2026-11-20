/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.AX
public import Logic.CTree.AF
public import Logic.CTree.AG
public import Logic.CTree.EX
public import Logic.CTree.EF
public import Logic.CTree.EG
public import Logic.Events.Writer

/-!
# Sequential composition on ctrees

Shallow next/until kernels exposing one real transition, the TICL rules for `bind` (prefix
formulas, native returns, until, up-to-bind for `AG`/`EG` in tower form) and the convenience rules
for logged instrumentation events `log s >>= fun _ => k` (← `CTree/Logic/Bind.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinduction Notation
open ITree (Effect)

/-! ## Shallow kernels -/

section Shallow
variable {E B : Effect.{u}} {X : Type u} {q : Ticlq} {P Q : CTree E B X → World E → Prop}
  {t : CTree E B X} {w : World E}

theorem quntil_unfold : quntil q P Q t w ↔ Q t w ∨ qnext q P (quntil q P Q) t w := by
  cases q
  · exact auc_unfold
  · exact euc_unfold

theorem qnext_vis_iff {e : E.I} {k : E.O e → CTree E B X} (y₀ : E.O e)
    (hlive : ∀ t w, P t w → NotDone w) :
    qnext q P Q (CTree.vis e k) w ↔
      P (CTree.vis e k) w ∧
        match q with
        | .A => ∀ y, Q (k y) (.obs e y)
        | .E => ∃ y, Q (k y) (.obs e y) := by
  cases q
  · refine ⟨fun ⟨hp, _, hn⟩ => ⟨hp, fun y => hn _ _ (ktrans_vis.2 ⟨y, rfl, rfl, hlive _ _ hp⟩)⟩,
      fun ⟨hp, hn⟩ => ⟨hp, (can_step_vis y₀).2 (hlive _ _ hp), fun t' w' tr => ?_⟩⟩
    obtain ⟨y, rfl, rfl, -⟩ := ktrans_vis.1 tr
    exact hn y
  · refine ⟨fun ⟨hp, t', w', tr, hq⟩ => ?_,
      fun ⟨hp, y, hq⟩ => ⟨hp, _, _, ktrans_vis.2 ⟨y, rfl, rfl, hlive _ _ hp⟩, hq⟩⟩
    obtain ⟨y, rfl, rfl, -⟩ := ktrans_vis.1 tr
    exact ⟨hp, y, hq⟩

theorem qnext_brS_iff {c : B.I} {k : B.O c → CTree E B X} (y₀ : B.O c)
    (hlive : ∀ t w, P t w → NotDone w) :
    qnext q P Q (CTree.brS c k) w ↔
      P (CTree.brS c k) w ∧
        match q with
        | .A => ∀ y, Q (k y) w
        | .E => ∃ y, Q (k y) w := by
  cases q
  · refine ⟨fun ⟨hp, _, hn⟩ => ⟨hp, fun y => hn _ _ (ktrans_brS.2 ⟨y, rfl, rfl, hlive _ _ hp⟩)⟩,
      fun ⟨hp, hn⟩ => ⟨hp, (can_step_brS y₀).2 (hlive _ _ hp), fun t' w' tr => ?_⟩⟩
    obtain ⟨y, rfl, rfl, -⟩ := ktrans_brS.1 tr
    exact hn y
  · refine ⟨fun ⟨hp, t', w', tr, hq⟩ => ?_,
      fun ⟨hp, y, hq⟩ => ⟨hp, _, _, ktrans_brS.2 ⟨y, rfl, rfl, hlive _ _ hp⟩, hq⟩⟩
    obtain ⟨y, rfl, rfl, -⟩ := ktrans_brS.1 tr
    exact ⟨hp, y, hq⟩

theorem qnext_step_iff (hlive : ∀ t w, P t w → NotDone w) :
    qnext q P Q (CTree.step t) w ↔ P (CTree.step t) w ∧ Q t w := by
  cases q
  · refine ⟨fun ⟨hp, _, hn⟩ => ⟨hp, hn _ _ (ktrans_step.2 ⟨rfl, rfl, hlive _ _ hp⟩)⟩,
      fun ⟨hp, hq⟩ => ⟨hp, can_step_step.2 (hlive _ _ hp), fun t' w' tr => ?_⟩⟩
    obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
    exact hq
  · refine ⟨fun ⟨hp, t', w', tr, hq⟩ => ?_,
      fun ⟨hp, hq⟩ => ⟨hp, _, _, ktrans_step.2 ⟨rfl, rfl, hlive _ _ hp⟩, hq⟩⟩
    obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
    exact ⟨hp, hq⟩

theorem qnext_dead_iff (hdead : ∀ u z, ¬ ktrans t w u z) : qnext q P Q t w ↔ False := by
  cases q
  · exact ⟨fun ⟨_, ⟨u, z, tr⟩, _⟩ => hdead u z tr, False.elim⟩
  · exact ⟨fun ⟨_, u, z, tr, _⟩ => hdead u z tr, False.elim⟩

theorem quntil_dead_iff (hdead : ∀ u z, ¬ ktrans t w u z) : quntil q P Q t w ↔ Q t w := by
  rw [quntil_unfold, qnext_dead_iff hdead, or_false]

theorem spin_no_ktrans : ∀ (u : CTree E B X) z, ¬ ktrans CTree.spin w u z :=
  fun _ _ tr => let ⟨_, tr, _⟩ := ktrans_trans.1 tr; spin_isStuck _ _ tr

end Shallow

theorem qnext_log_iff {W : Type u} {B : Effect.{u}} {X : Type u} {q : Ticlq}
    {P Q : ctreeW W B X → World (writerE W) → Prop} {o : W} {t : ctreeW W B X}
    {w : World (writerE W)} (hlive : ∀ t w, P t w → NotDone w) :
    qnext q P Q (log o >>= fun _ => t) w ↔
      P (log o >>= fun _ => t) w ∧ Q t (.obs (E := writerE W) o ⟨⟩) := by
  rw [log_vis, qnext_vis_iff (E := writerE W) (e := o) PUnit.unit hlive]
  cases q
  · exact and_congr_right fun _ => ⟨fun h => h ⟨⟩, fun h _ => h⟩
  · exact and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩

theorem quntil_log_iff {W : Type u} {B : Effect.{u}} {X : Type u} {q : Ticlq}
    {P Q : ctreeW W B X → World (writerE W) → Prop} {o : W} {t : ctreeW W B X}
    {w : World (writerE W)} (hlive : ∀ t w, P t w → NotDone w) :
    quntil q P Q (log o >>= fun _ => t) w ↔
      Q (log o >>= fun _ => t) w ∨
        (P (log o >>= fun _ => t) w ∧ quntil q P Q t (.obs (E := writerE W) o ⟨⟩)) :=
  quntil_unfold.trans (or_congr_right (qnext_log_iff hlive))

theorem qnext_sb {E B : Effect.{u}} {X : Type u} {q : Ticlq}
    {P Q : CTree E B X → World E → Prop} {w : World E}
    (hP : SbProper P) (hQ : SbProper Q) {t u : CTree E B X} (h : t ~ u) :
    qnext q P Q t w ↔ qnext q P Q u w :=
  proper_qnext_equ (meq := (· ~ ·)) (fun _ _ w h => hP w h) (fun _ _ w h => hQ w h) q h

theorem quntil_sb {E B : Effect.{u}} {X : Type u} {q : Ticlq}
    {P Q : CTree E B X → World E → Prop} {w : World E}
    (hP : SbProper P) (hQ : SbProper Q) {t u : CTree E B X} (h : t ~ u) :
    quntil q P Q t w ↔ quntil q P Q u w :=
  proper_quntil_equ (meq := (· ~ ·)) (fun _ _ w h => hP w h) (fun _ _ w h => hQ w h) q h

/-! ## Bind rules -/

section BindLemmas
variable {E B : Effect.{u}} {X Y : Type u} {i : Option (Type u)} {w : World E}
  {t : CTree E B Y} {k : Y → CTree E B X}

private theorem not_done_eq {y : Y} {w : World E} (hd : done_eq y w) (h : NotDone w) : False := by
  cases hd <;> cases h

private theorem ticll_bind_l_aux {i : Option (Type u)} (φ : Ticl E i) (hi : i = none)
    {t : CTree E B Y} {w : World E} (h : entails φ t w) : entails φ (t >>= k) w := by
  induction φ generalizing t w with
  | now p => exact h
  | ret p => cases hi
  | cu q p r ihp ihr =>
    cases q
    · change Auc _ _ t w at h
      induction h with
      | matchA h => exact Auc.matchA (ihr hi h)
      | stepA hp hs hk ih =>
        obtain ⟨t₁, w₁, tr₁⟩ := hs
        refine Auc.stepA (ihp rfl hp)
          (can_step_bind_l tr₁ (ticl_not_done (.cu .A p r) (hk _ _ tr₁))) fun u z htr => ?_
        rcases ktrans_bind_inv htr with ⟨v, tr, -, rfl⟩ | ⟨y, w₀, tr, hd, -⟩
        · exact ih _ _ tr
        · exact (not_done_eq hd (ticl_not_done (.cu .A p r) (hk _ _ tr))).elim
    · change Euc _ _ t w at h
      induction h with
      | matchE h => exact Euc.matchE (ihr hi h)
      | stepE t' w' hp tr h ih =>
        exact Euc.stepE _ w' (ihp rfl hp) (ktrans_bind_l tr (ticl_not_done (.cu .E p r) h)) ih
  | cx q p r ihp ihr =>
    cases q
    · obtain ⟨hp, ⟨t₁, w₁, tr₁⟩, hk⟩ := h
      refine ⟨ihp rfl hp, can_step_bind_l tr₁ (ticl_not_done r (hk _ _ tr₁)), fun u z htr => ?_⟩
      rcases ktrans_bind_inv htr with ⟨v, tr, -, rfl⟩ | ⟨y, w₀, tr, hd, -⟩
      · exact ihr hi (hk _ _ tr)
      · exact (not_done_eq hd (ticl_not_done r (hk _ _ tr))).elim
    · obtain ⟨hp, t', w', tr, hr⟩ := h
      exact ⟨ihp rfl hp, _, w', ktrans_bind_l tr (ticl_not_done r hr), ihr hi hr⟩
  | cg q p ihp =>
    cases q
    · let Z : CTree E B X → World E → Prop := fun u z => ∃ t₀, u = t₀ >>= k ∧ agc (entails p) t₀ z
      refine le_gfp (b := agcF (entails p)) (x := Z) ?_ _ _ ⟨t, rfl, h⟩
      rintro _ z ⟨t₀, rfl, h⟩
      obtain ⟨hp, ⟨t₁, w₁, tr₁⟩, hk⟩ := agc_unfold.1 h
      refine ⟨ihp rfl hp, can_step_bind_l tr₁ (ticl_not_done (.cg .A p) (hk _ _ tr₁)),
        fun u z' htr => ?_⟩
      rcases ktrans_bind_inv htr with ⟨v, tr, -, rfl⟩ | ⟨y, w₀, tr, hd, -⟩
      · exact ⟨v, rfl, hk _ _ tr⟩
      · exact (not_done_eq hd (ticl_not_done (.cg .A p) (hk _ _ tr))).elim
    · let Z : CTree E B X → World E → Prop := fun u z => ∃ t₀, u = t₀ >>= k ∧ egc (entails p) t₀ z
      refine le_gfp (b := egcF (entails p)) (x := Z) ?_ _ _ ⟨t, rfl, h⟩
      rintro _ z ⟨t₀, rfl, h⟩
      obtain ⟨hp, t', w', tr, h'⟩ := egc_unfold.1 h
      exact ⟨ihp rfl hp, _, w', ktrans_bind_l tr (ticl_not_done (.cg .E p) h'), t', rfl, h'⟩
  | and p r ihp ihr => exact ⟨ihp hi h.1, ihr hi h.2⟩
  | or p r ihp ihr => exact h.imp (ihp hi) (ihr hi)

/-- If `t` satisfies the prefix formula `φ`, so do all its extensions `t >>= k`. -/
theorem ticll_bind_l {φ : TiclL E} (h : entails φ t w) : entails φ (t >>= k) w :=
  ticll_bind_l_aux φ rfl h

/-- A native return hands the complete indexed obligation to the continuation. -/
theorem ticl_bind_ret {p : Ticl E i} {R : Y → World E → Prop} (h : entails (.ret R) t w)
    (hk : ∀ y w', R y w' → entails p (k y) w') : entails p (t >>= k) w := by
  obtain ⟨x, hR, hsb⟩ := ret_sbisim h
  refine (proper_entails_meq p (sbisim_clo_bind_eq hsb fun _ => sbisim_refl _)).2 ?_
  rw [pure_bind']
  exact hk x w hR

theorem ticl_bind_ret_eq {p : Ticl E i} {r : Y} {wr : World E}
    (h : entails (.ret fun y z => r = y ∧ wr = z) t w) (hk : entails p (k r) wr) :
    entails p (t >>= k) w :=
  ticl_bind_ret h fun _ _ ⟨hy, hz⟩ => hy ▸ hz ▸ hk

theorem an_bind_l {φ : TiclL E} {ψ : Ticl E i} {R : Y → World E → Prop}
    (h : entails (φ AN .ret R) t w) (hk : ∀ y w', R y w' → entails ψ (k y) w') :
    entails (φ AN ψ) (t >>= k) w := by
  obtain ⟨hp, ⟨t₁, w₁, tr₁⟩, hn⟩ := h
  refine ⟨ticll_bind_l hp, can_step_bind_l tr₁ (ticl_not_done _ (hn _ _ tr₁)), fun u z htr => ?_⟩
  rcases ktrans_bind_inv htr with ⟨v, tr, -, rfl⟩ | ⟨y, w₀, tr, hd, -⟩
  · exact ticl_bind_ret (hn _ _ tr) hk
  · exact (not_done_eq hd (ticl_not_done _ (hn _ _ tr))).elim

theorem u_bind_r {q : Ticlq} {φ : TiclL E} {ψ : Ticl E i} {R : Y → World E → Prop}
    (h : entails (.cu q φ (.ret R)) t w) (hk : ∀ y w', R y w' → entails (.cu q φ ψ) (k y) w') :
    entails (.cu q φ ψ) (t >>= k) w := by
  cases q
  · change Auc _ _ t w at h
    induction h with
    | matchA h => exact ticl_bind_ret h hk
    | stepA hp hs hn ih =>
      obtain ⟨t₁, w₁, tr₁⟩ := hs
      refine Auc.stepA (ticll_bind_l hp)
        (can_step_bind_l tr₁ (ticl_not_done (.cu .A φ (.ret R)) (hn _ _ tr₁))) fun u z htr => ?_
      rcases ktrans_bind_inv htr with ⟨v, tr, -, rfl⟩ | ⟨y, w₀, tr, hd, -⟩
      · exact ih _ _ tr
      · exact (not_done_eq hd (ticl_not_done (.cu .A φ (.ret R)) (hn _ _ tr))).elim
  · change Euc _ _ t w at h
    induction h with
    | matchE h => exact ticl_bind_ret h hk
    | stepE t' w' hp tr h ih =>
      exact Euc.stepE _ w' (ticll_bind_l hp)
        (ktrans_bind_l tr (ticl_not_done (.cu .E φ (.ret R)) h)) ih

theorem u_bind_r_eq {q : Ticlq} {φ : TiclL E} {ψ : Ticl E i} {r : Y} {wr : World E}
    (h : entails (.cu q φ (.ret fun y z => r = y ∧ wr = z)) t w)
    (hk : entails (.cu q φ ψ) (k r) wr) : entails (.cu q φ ψ) (t >>= k) w :=
  u_bind_r h fun _ _ ⟨hy, hz⟩ => hy ▸ hz ▸ hk

theorem ax_au_bind_r {φ : TiclL E} {ψ : Ticl E i} {R : Y → World E → Prop}
    (h : entails (AX (φ AU .ret R)) t w) (hk : ∀ y w', R y w' → entails (φ AU ψ) (k y) w') :
    entails (AX (φ AU ψ)) (t >>= k) w := by
  obtain ⟨hp, ⟨t₁, w₁, tr₁⟩, hn⟩ := h
  refine ⟨ticll_bind_l hp, can_step_bind_l tr₁ (ticl_not_done _ (hn _ _ tr₁)), fun u z htr => ?_⟩
  rcases ktrans_bind_inv htr with ⟨v, tr, -, rfl⟩ | ⟨y, w₀, tr, hd, -⟩
  · exact u_bind_r (hn _ _ tr) hk
  · exact (not_done_eq hd (ticl_not_done _ (hn _ _ tr))).elim

/-- A fixed terminal result on every successor is exactly native return. -/
theorem ret_done_eq_iff {t : CTree E B X} {r : X} {wr : World E} :
    anc (entails (⊤ : TiclL E)) (fun _ wd => DoneWith (fun x z => r = x ∧ wr = z) wd) t w ↔
      entails (.ret fun x z => r = x ∧ wr = z) t w := by
  refine ⟨fun ⟨htop, hs, htr⟩ => ?_, ret_done_next _⟩
  obtain ⟨t', wd, tr⟩ := hs
  have hw : wr = w := by
    cases htr t' wd tr with
    | done x h => exact h.2.trans (ktrans_to_done_inv tr).2.symm
    | finish e v x h => exact h.2.trans (ktrans_to_finish_inv tr).2.symm
  subst hw
  exact ⟨r, ⟨rfl, rfl⟩, htop.2, ⟨t', wd, tr⟩, fun t' wd tr => (done_of_eq r wr wd).2 (htr t' wd tr)⟩

/-! ### Up-to bind principles for `AG` and `EG` (tower form)

Every element `R` of the final chain of `agcF (entails φ)` is closed under sequencing a prefix
that satisfies `φ` until it returns with postcondition `Post`, provided the continuation lands in
`R`. The `gfp` itself is a chain element (`gfp_chain`). -/

theorem ag_bind_chain {φ : TiclL E} {Post : Y → World E → Prop} {R : Rel (CTree E B X) (World E)}
    (hR : Chain (agcF (entails φ)) R) (h : entails (φ AU .ret Post) t w)
    (hk : ∀ x w, Post x w → R (k x) w) : R (t >>= k) w := by
  revert t k w
  refine tower (P := fun R : Rel (CTree E B X) (World E) =>
      ∀ {t : CTree E B Y} {k : Y → CTree E B X} {w : World E},
      entails (φ AU .ret Post) t w → (∀ x w, Post x w → R (k x) w) → R (t >>= k) w)
    (fun T hT t k w h hk => Rel.inf_apply.2 fun R hR =>
      hT R hR h fun x w hp => Rel.inf_apply.1 (hk x w hp) R hR) ?_ R hR
  intro R hR ih t k w h hk
  match (h : Auc _ _ t w) with
  | .matchA h =>
    obtain ⟨x, hp, hsb⟩ := ret_sbisim h
    refine (proper_ax_equ (P := entails φ) (Q := R) (fun _ _ _ h => proper_entails_meq φ h)
      (fun _ _ _ h => agc_chain_proper (P := entails φ) (fun _ _ _ h => proper_entails_meq φ h)
        R hR _ _ _ h)
      (sbisim_clo_bind_eq hsb fun _ => sbisim_refl _)).2 ?_
    rw [pure_bind']
    exact hk x w hp
  | .stepA hp ⟨t₁, w₁, tr₁⟩ hn =>
    refine ⟨ticll_bind_l hp, can_step_bind_l tr₁ (ticl_not_done (φ AU .ret Post) (hn _ _ tr₁)),
      fun u z htr => ?_⟩
    rcases ktrans_bind_inv htr with ⟨v, tr, -, rfl⟩ | ⟨y, w₀, tr, hd, -⟩
    · exact ih (hn _ _ tr) fun x w hp => b_chain hR _ _ (hk x w hp)
    · exact (not_done_eq hd (ticl_not_done (φ AU .ret Post) (hn _ _ tr))).elim

/-- Structural up-to bind rule for `AG`: `t` satisfies `φ` until it returns with postcondition
`R`, and every continuation allowed by `R` satisfies `AG φ`. -/
theorem ag_bind_r {φ : TiclL E} {R : Y → World E → Prop} (h : entails (φ AU .ret R) t w)
    (hk : ∀ x w, R x w → entails (AG φ) (k x) w) : entails (AG φ) (t >>= k) w :=
  ag_bind_chain (gfp_chain _) h hk

theorem eg_bind_chain {φ : TiclL E} {Post : Y → World E → Prop} {R : Rel (CTree E B X) (World E)}
    (hR : Chain (egcF (entails φ)) R) (h : entails (φ EU .ret Post) t w)
    (hk : ∀ x w, Post x w → R (k x) w) : R (t >>= k) w := by
  revert t k w
  refine tower (P := fun R : Rel (CTree E B X) (World E) =>
      ∀ {t : CTree E B Y} {k : Y → CTree E B X} {w : World E},
      entails (φ EU .ret Post) t w → (∀ x w, Post x w → R (k x) w) → R (t >>= k) w)
    (fun T hT t k w h hk => Rel.inf_apply.2 fun R hR =>
      hT R hR h fun x w hp => Rel.inf_apply.1 (hk x w hp) R hR) ?_ R hR
  intro R hR ih t k w h hk
  match (h : Euc _ _ t w) with
  | .matchE h =>
    obtain ⟨x, hp, hsb⟩ := ret_sbisim h
    refine (proper_ex_equ (P := entails φ) (Q := R) (fun _ _ _ h => proper_entails_meq φ h)
      (fun _ _ _ h => egc_chain_proper (P := entails φ) (fun _ _ _ h => proper_entails_meq φ h)
        R hR _ _ _ h)
      (sbisim_clo_bind_eq hsb fun _ => sbisim_refl _)).2 ?_
    rw [pure_bind']
    exact hk x w hp
  | .stepE t' w' hp tr h' =>
    exact ⟨ticll_bind_l hp, _, w', ktrans_bind_l tr (ticl_not_done (φ EU .ret Post) h'),
      ih h' fun x w hp => b_chain hR _ _ (hk x w hp)⟩

/-- Structural up-to bind rule for `EG`. -/
theorem eg_bind_r {φ : TiclL E} {R : Y → World E → Prop} (h : entails (φ EU .ret R) t w)
    (hk : ∀ r w', R r w' → entails (EG φ) (k r) w') : entails (EG φ) (t >>= k) w :=
  eg_bind_chain (gfp_chain _) h hk

/-- `eg_bind_r` for a deterministic prefix (`ret= r wr`). -/
theorem eg_bind_r_eq {φ : TiclL E} {r : Y} {wr : World E} (h : entails (φ EU ret= r wr) t w)
    (hk : entails (EG φ) (k r) wr) : entails (EG φ) (t >>= k) w :=
  eg_bind_r h fun _ _ ⟨hy, hz⟩ => hy ▸ hz ▸ hk

end BindLemmas

/-! ## Logged instrumentation events -/

section LogLemmas
variable {B : Effect.{u}} {X W : Type u} {i : Option (Type u)} {s : W} {k : ctreeW W B X}
  {w : World (writerE W)} {φ : TiclL (writerE W)} {ψ : Ticl (writerE W) i}

/-- A log has one successor, at its recorded observation world. -/
theorem an_log_iff :
    entails (φ AN ψ) (log s >>= fun _ => k) w ↔
      entails φ (log s >>= fun _ => k) w ∧ entails ψ k (.obs (E := writerE W) s ⟨⟩) :=
  qnext_log_iff (q := .A) fun _ _ h => ticl_not_done φ h

theorem en_log_iff :
    entails (φ EN ψ) (log s >>= fun _ => k) w ↔
      entails φ (log s >>= fun _ => k) w ∧ entails ψ k (.obs (E := writerE W) s ⟨⟩) :=
  qnext_log_iff (q := .E) fun _ _ h => ticl_not_done φ h

theorem au_log_iff :
    entails (φ AU ψ) (log s >>= fun _ => k) w ↔
      entails ψ (log s >>= fun _ => k) w ∨
        (entails φ (log s >>= fun _ => k) w ∧
          entails (φ AU ψ) k (.obs (E := writerE W) s ⟨⟩)) :=
  (quntil_unfold (q := .A)).trans (or_congr_right (an_log_iff (φ := φ) (ψ := φ AU ψ)))

theorem eu_log_iff :
    entails (φ EU ψ) (log s >>= fun _ => k) w ↔
      entails ψ (log s >>= fun _ => k) w ∨
        (entails φ (log s >>= fun _ => k) w ∧
          entails (φ EU ψ) k (.obs (E := writerE W) s ⟨⟩)) :=
  (quntil_unfold (q := .E)).trans (or_congr_right (en_log_iff (φ := φ) (ψ := φ EU ψ)))

theorem ag_log_iff :
    entails (AG φ) (log s >>= fun _ => k) w ↔
      entails φ (log s >>= fun _ => k) w ∧ entails (AG φ) k (.obs (E := writerE W) s ⟨⟩) :=
  agc_unfold.trans (an_log_iff (φ := φ) (ψ := AG φ))

theorem eg_log_iff :
    entails (EG φ) (log s >>= fun _ => k) w ↔
      entails φ (log s >>= fun _ => k) w ∧ entails (EG φ) k (.obs (E := writerE W) s ⟨⟩) :=
  egc_unfold.trans (en_log_iff (φ := φ) (ψ := EG φ))

theorem an_log (hψ : entails ψ k (.obs (E := writerE W) s ⟨⟩))
    (hφ : entails φ (log s >>= fun _ => k) w) : entails (φ AN ψ) (log s >>= fun _ => k) w :=
  an_log_iff.2 ⟨hφ, hψ⟩

theorem ax_log (hd : NotDone w) (hψ : entails ψ k (.obs (E := writerE W) s ⟨⟩)) :
    entails (AX ψ) (log s >>= fun _ => k) w :=
  an_log hψ ⟨trivial, hd⟩

theorem au_log (hψ : entails (φ AU ψ) k (.obs (E := writerE W) s ⟨⟩))
    (hφ : entails φ (log s >>= fun _ => k) w) : entails (φ AU ψ) (log s >>= fun _ => k) w :=
  au_log_iff.2 (.inr ⟨hφ, hψ⟩)

theorem af_log (hd : NotDone w) (hψ : entails (AF ψ) k (.obs (E := writerE W) s ⟨⟩)) :
    entails (AF ψ) (log s >>= fun _ => k) w :=
  au_log hψ ⟨trivial, hd⟩

theorem en_log (hψ : entails ψ k (.obs (E := writerE W) s ⟨⟩))
    (hφ : entails φ (log s >>= fun _ => k) w) : entails (φ EN ψ) (log s >>= fun _ => k) w :=
  en_log_iff.2 ⟨hφ, hψ⟩

theorem eu_log (hψ : entails (φ EU ψ) k (.obs (E := writerE W) s ⟨⟩))
    (hφ : entails φ (log s >>= fun _ => k) w) : entails (φ EU ψ) (log s >>= fun _ => k) w :=
  eu_log_iff.2 (.inr ⟨hφ, hψ⟩)

theorem ef_log (hd : NotDone w) (hψ : entails (EF ψ) k (.obs (E := writerE W) s ⟨⟩)) :
    entails (EF ψ) (log s >>= fun _ => k) w :=
  eu_log hψ ⟨trivial, hd⟩

end LogLemmas

-- Not ported: nothing. `qnext_{vis,brS,log,step}_iff` drop Rocq's `Proper` hypotheses `HP`/`HQ`:
-- they only served `equ` rewriting, which is `=` here (the statements are strictly stronger).

end Tisl
