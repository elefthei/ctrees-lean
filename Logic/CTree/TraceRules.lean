/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Trace
public import Logic.CTree.Iter
public import Logic.CTree.Sim

/-!
# Temporal rules for traces

Productive step/log families, eventually and recurrently taken transition labels
(`EventuallyLabel`, `RecurrentLabel`), the `AF`/`AG` rules of finite log prefixes (`emit_list`)
and of repeating observation batches (`emit_batches`) (← `CTree/Logic/Trace.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinduction Notation
open ITree (Effect)

variable {E B : Effect.{u}} {W I X : Type u}

/-! ## Productive families -/

/-- A family of visible steps is productive but preserves the observation world. -/
theorem ag_step_family (family : I → CTree E B X) (next : I → I)
    (hstep : ∀ i, family i ~ .step (family (next i))) :
    ∀ i w, NotDone w → entails (AG (⊤ : TiclL E)) (family i) w := by
  suffices H : ∀ j t w, t ~ family j → NotDone w → entails (AG (⊤ : TiclL E)) t w from
    fun i w hw => H i _ w (sbisim_refl _) hw
  coinduction R _ cih
  intro j t w ht hw
  have ht' := sbisim_trans ht (hstep j)
  refine ⟨⟨trivial, hw⟩, (proper_can_step ht').2 (can_step_step.2 hw), fun t' w' tr => ?_⟩
  obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht' tr
  obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
  exact cih (next j) t' w hu hw

/-- A family of visible steps never reaches a matching observation from `pure`. -/
theorem step_family_no_ef_visible (family : I → ctreeW W B X) (next : I → I)
    (hstep : ∀ i, family i ~ .step (family (next i))) (P : W → Prop) :
    ∀ i, ¬ entails (EF (visWₜ P)) (family i) .pure := by
  suffices h : ∀ t w, entails (EF (visWₜ P)) t w → ∀ j, t ~ family j → w = .pure → False from
    fun i he => h _ _ he i (sbisim_refl _) rfl
  intro t w he
  induction he with
  | matchE hv => rintro j - rfl; cases hv.1
  | stepE t' w' _ tr _ ih =>
    rintro j ht rfl
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper (sbisim_trans ht (hstep j)) tr
    obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
    exact ih (next j) hu rfl

/-- A logged family remains productive while changing the world. -/
theorem ag_log_family (family : I → ctreeW W B X) (next : I → I) (pick : I → W)
    (hlog : ∀ i, family i ~ .vis (E := writerE W) (pick i) fun _ => family (next i)) :
    ∀ i w, NotDone w → entails (AG (⊤ : TiclL (writerE W))) (family i) w := by
  suffices H : ∀ j t w, t ~ family j → NotDone w →
      entails (AG (⊤ : TiclL (writerE W))) t w from
    fun i w hw => H i _ w (sbisim_refl _) hw
  coinduction R _ cih
  intro j t w ht hw
  have ht' := sbisim_trans ht (hlog j)
  refine ⟨⟨trivial, hw⟩, (proper_can_step ht').2
    ((can_step_vis (E := writerE W) (e := pick j) ⟨⟩).2 hw), fun t' w' tr => ?_⟩
  obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht' tr
  obtain ⟨_, hw', rfl, -⟩ := ktrans_vis.1 tr
  exact cih (next j) t' w' hu (hw' ▸ .obs _ _)

/-- A family logging only rejected payloads never reaches a matching observation. -/
theorem log_family_no_ef_visible (family : I → ctreeW W B X) (next : I → I) (pick : I → W)
    (hlog : ∀ i, family i ~ .vis (E := writerE W) (pick i) fun _ => family (next i))
    (P : W → Prop) (hreject : ∀ i, ¬ P (pick i)) :
    ∀ i, ¬ entails (EF (visWₜ P)) (family i) .pure := by
  suffices h : ∀ t w, entails (EF (visWₜ P)) t w → ∀ j, t ~ family j →
      (w = .pure ∨ ∃ k, w = .obs (E := writerE W) (pick k) ⟨⟩) → False from
    fun i he => h _ _ he i (sbisim_refl _) (.inl rfl)
  intro t w he
  induction he with
  | matchE hv =>
    rintro j - (rfl | ⟨k, rfl⟩)
    · cases hv.1
    · cases hv.1 with | obs _ _ h => exact hreject k h
  | stepE t' w' _ tr _ ih =>
    intro j ht _
    obtain ⟨u, tr, hu⟩ := ktrans_semiproper (sbisim_trans ht (hlog j)) tr
    obtain ⟨⟨⟩, rfl, rfl, -⟩ := ktrans_vis.1 tr
    exact ih (next j) hu (.inr ⟨j, rfl⟩)

/-! ## Eventually and recurrently taken labels -/

/-- Productive universal recurrence of actual transition labels (Rocq `eventually_label`): `t` can
move, and every transition either carries a `P` label or leads to a tree that eventually does.
Lean rejects Rocq's nested `P l ∨ …` premise, so the constructor takes the classically
equivalent `¬ P l → …`; `eventually_label_intro` is the Rocq constructor. -/
inductive EventuallyLabel (P : Label E → Prop) : CTree E B X → Prop
  | intro {t : CTree E B X} : can_trans t →
      (∀ l u, trans l t u → ¬ P l → EventuallyLabel P u) → EventuallyLabel P t

/-- The Rocq constructor `eventually_label_intro`. -/
theorem eventually_label_intro {P : Label E → Prop} {t : CTree E B X} (hcan : can_trans t)
    (hnext : ∀ l u, trans l t u → P l ∨ EventuallyLabel P u) : EventuallyLabel P t :=
  .intro hcan fun l u tr hl => (hnext l u tr).resolve_left hl

/-- Rocq's induction principle retaining the nested continuation proof. -/
theorem eventually_label_ind (P : Label E → Prop) (R : CTree E B X → Prop)
    (hstep : ∀ t, can_trans t →
      (∀ l u, trans l t u → P l ∨ (EventuallyLabel P u ∧ R u)) → R t) :
    ∀ t, EventuallyLabel P t → R t := by
  intro t h
  induction h with
  | intro hcan hnext ih =>
    refine hstep _ hcan fun l u tr => ?_
    by_cases hl : P l
    · exact .inl hl
    · exact .inr ⟨hnext l u tr hl, ih l u tr hl⟩

/-- The functor of `RecurrentLabel`. -/
def recurrentLabelF (P : Label E → Prop) : Mon (Pred (CTree E B X)) where
  body R t := EventuallyLabel P t ∧ ∀ l u, trans l t u → R u
  mono h _ H := ⟨H.1, fun l u tr => h _ (H.2 l u tr)⟩

/-- Every reachable tree eventually takes a `P` label (Rocq coinductive `recurrent_label`). -/
def RecurrentLabel (P : Label E → Prop) : CTree E B X → Prop := gfp (recurrentLabelF P)

theorem recurrent_label_unfold {P : Label E → Prop} {t : CTree E B X} :
    RecurrentLabel P t ↔ EventuallyLabel P t ∧ ∀ l u, trans l t u → RecurrentLabel P u :=
  ⟨fun h => gfp_pfp (b := recurrentLabelF P) t h,
   fun h => b_chain (gfp_chain (recurrentLabelF P)) t h⟩

/-- The Rocq constructor `recurrent_label_intro`. -/
theorem recurrent_label_intro {P : Label E → Prop} {t : CTree E B X} (he : EventuallyLabel P t)
    (hnext : ∀ l u, trans l t u → RecurrentLabel P u) : RecurrentLabel P t :=
  recurrent_label_unfold.2 ⟨he, hnext⟩

/-- Labels logging a payload that satisfies `P`. -/
def log_label (P : W → Prop) : Label (writerE W) → Prop
  | .obs o _ => P o
  | _ => False

theorem eventually_label_sbisim (P : Label E → Prop) (t u : CTree E B X) :
    t ~ u → EventuallyLabel P t → EventuallyLabel P u := by
  intro hsb h
  induction h generalizing u with
  | intro hcan _ ih =>
    obtain ⟨hf, hb⟩ := sbisim_unfold.1 hsb
    refine .intro ?_ fun l v tr hl => ?_
    · obtain ⟨l, t', tr⟩ := hcan
      obtain ⟨_, v', tr', -, rfl⟩ := hf _ _ tr
      exact ⟨_, v', tr'⟩
    · obtain ⟨_, t', tr', hv, rfl⟩ := hb _ _ tr
      exact ih _ _ tr' hl _ hv

theorem recurrent_label_sbisim (P : Label E → Prop) (t u : CTree E B X) :
    t ~ u → RecurrentLabel P t → RecurrentLabel P u := by
  revert t u
  coinduction R _ cih
  intro t u hsb h
  obtain ⟨he, hnext⟩ := recurrent_label_unfold.1 h
  refine ⟨eventually_label_sbisim P t u hsb he, fun l v tr => ?_⟩
  obtain ⟨_, t', tr', hv, rfl⟩ := (sbisim_unfold.1 hsb).2 _ _ tr
  exact cih t' v hv (hnext _ _ tr')

/-- A false remembered target forces a future matching label. -/
theorem af_vis_eventually_label {B : Effect.{u}} (P Q : W → Prop) (P_dec : ∀ o, Decidable (P o))
    (Q_P : ∀ o, Q o → P o) (t : ctreeW W B X) (w : World (writerE W)) :
    ¬ entails (visWₜ Q) t w → entails (AF (visWₜ Q)) t w → EventuallyLabel (log_label P) t := by
  intro hfalse haf
  induction haf with
  | matchA h => exact absurd h hfalse
  | @stepA t w htop hcan hnext ih =>
    have hd : NotDone w := htop.2
    refine eventually_label_intro ?_ fun l u tr => ?_
    · obtain ⟨u, w', tr⟩ := hcan
      obtain ⟨l, tr, -⟩ := ktrans_trans.1 tr
      exact ⟨l, u, tr⟩
    · cases l with
      | tau => exact .inr (ih u w (.tau hd tr) hfalse)
      | obs o v =>
        match P_dec o with
        | isTrue hit => exact .inl hit
        | isFalse hmiss =>
          refine .inr (ih u _ (.obs o v hd tr) fun h => ?_)
          cases h.1 with | obs _ _ hq => exact hmiss (Q_P _ hq)
      | val x =>
        obtain rfl := trans_val_invT tr
        exfalso
        cases hd with
        | pure => exact nomatch ticl_not_done (AF (visWₜ Q)) (hnext u _ (.done x tr))
        | obs e v => exact nomatch ticl_not_done (AF (visWₜ Q)) (hnext u _ (.finish e v x tr))

/-- A separating family of fresh `AG (AF visW (Q k))` targets yields recurrent `P` labels; the
proof-private target is refreshed at every continuation, including hits. -/
theorem agaf_family_recurrent_label {B : Effect.{u}} (P : W → Prop) (Q : Nat → W → Prop)
    (P_dec : ∀ o, Decidable (P o)) (Q_P : ∀ k o, Q k o → P o)
    (Q_separates : ∀ o, ∃ k, ¬ Q k o) (t : ctreeW W B X) (w : World (writerE W)) :
    (∀ k, entails (AG (AF (visWₜ (Q k)))) t w) → RecurrentLabel (log_label P) t := by
  revert t w
  coinduction R _ cih
  intro t w hfam
  have hlive : NotDone w := ticl_not_done _ (hfam 0)
  have hcut : ∃ k, ¬ entails (visWₜ (Q k)) t w := by
    cases hlive with
    | pure => exact ⟨0, fun h => nomatch h.1⟩
    | obs o v =>
      obtain ⟨k, hmiss⟩ := Q_separates o
      exact ⟨k, fun h => by cases h.1 with | obs _ _ hq => exact hmiss hq⟩
  obtain ⟨k, hfalse⟩ := hcut
  refine ⟨af_vis_eventually_label P (Q k) P_dec (Q_P k) t w hfalse
    (agc_unfold.1 (hfam k)).1, fun l u tr => ?_⟩
  have hnext k' := (agc_unfold.1 (hfam k')).2.2
  cases l with
  | tau => exact cih u w fun k' => hnext k' u w (.tau hlive tr)
  | obs o v => exact cih u _ fun k' => hnext k' u _ (.obs o v hlive tr)
  | val x =>
    obtain rfl := trans_val_invT tr
    exfalso
    cases hlive with
    | pure => exact nomatch ticl_not_done (AG (AF (visWₜ (Q 0)))) (hnext 0 u _ (.done x tr))
    | obs e v =>
      exact nomatch ticl_not_done (AG (AF (visWₜ (Q 0)))) (hnext 0 u _ (.finish e v x tr))

/-! ## Temporal properties of finite observation prefixes -/

theorem f_emit_list {B : Effect.{u}} {i : Option (Type u)} (q : Ticlq) (xs : List W)
    (t : ctreeW W B X) (w : World (writerE W)) (ψ : Ticl (writerE W) i) :
    NotDone w → entails (.cu q ⊤ ψ) t (after_logs xs w) →
      entails (.cu q ⊤ ψ) (emit_list xs t) w := by
  induction xs generalizing w with
  | nil => exact fun _ h => h
  | cons o rest ih =>
    intro hd h
    have h' := ih (.obs (E := writerE W) o ⟨⟩) (.obs _ _) h
    show entails _ (log o >>= fun _ => emit_list rest t) w
    cases q
    · exact af_log hd h'
    · exact ef_log hd h'

theorem af_emit_list {B : Effect.{u}} (xs : List W) (t : ctreeW W B X) (w : World (writerE W))
    (P : W → Prop) : NotDone w → entails (AF (visWₜ P)) t (after_logs xs w) →
      entails (AF (visWₜ P)) (emit_list xs t) w :=
  f_emit_list .A xs t w _

theorem agaf_emit_list {B : Effect.{u}} (xs : List W) (t : ctreeW W B X) (w : World (writerE W))
    (P : W → Prop) : NotDone w → entails (AG (AF (visWₜ P))) t (after_logs xs w) →
      entails (AG (AF (visWₜ P))) (emit_list xs t) w := by
  induction xs generalizing w with
  | nil => exact fun _ h => h
  | cons o rest ih =>
    intro hd h
    have htail := ih (.obs (E := writerE W) o ⟨⟩) (.obs _ _) h
    exact ag_log_iff.2 ⟨af_log hd (agc_unfold.1 htail).1, htail⟩

theorem af_emit_list_member {B : Effect.{u}} (xs : List W) (t : ctreeW W B X)
    (w : World (writerE W)) (P : W → Prop) (o : W) :
    NotDone w → o ∈ xs → P o → entails (AF (visWₜ P)) (emit_list xs t) w := by
  induction xs generalizing w with
  | nil => exact fun _ h => nomatch h
  | cons a rest ih =>
    intro hd hin hp
    show entails _ (log a >>= fun _ => emit_list rest t) w
    refine af_log hd ?_
    cases hin with
    | head => exact .matchA ⟨.obs _ _ hp, .obs _ _⟩
    | tail _ hin => exact ih _ (.obs _ _) hin hp

theorem af_emit_list_ret {B : Effect.{u}} (xs : List W) (r : X) (w : World (writerE W))
    (Q : X → World (writerE W) → Prop) :
    NotDone w → Q r (after_logs xs w) →
      entails (AF (.ret Q)) (emit_list (B := B) xs (pure r)) w :=
  fun hd hQ => f_emit_list .A xs _ w _ hd (.matchA (ret_ret (after_logs_not_done xs hd) hQ))

/-- Removing a finite log prefix retains the nested formula on the tail at the final
observation world. -/
theorem ag_emit_list_suffix {B : Effect.{u}} (xs : List W) (t : ctreeW W B X)
    (w : World (writerE W)) (φ : TiclL (writerE W)) :
    entails (AG φ) (emit_list xs t) w → entails (AG φ) t (after_logs xs w) := by
  induction xs generalizing w with
  | nil => exact id
  | cons o rest ih => exact fun h => ih _ (ag_log_iff.1 h).2

theorem ag_emit_list_stuck {B : Effect.{u}} (xs : List W) (w : World (writerE W))
    (φ : TiclL (writerE W)) : ¬ entails (AG φ) (emit_list xs (CTree.stuck : ctreeW W B X)) w :=
  fun h => ag_stuck (ag_emit_list_suffix xs _ w φ h)

/-- A retained observation `stamp a j` cannot satisfy a freshness predicate bounded below by
`j + 1`: an `AF` of that formula is not discharged by the world in hand. -/
theorem indexed_excludes_retained {A : Type u} {B : Effect.{u}} (t : ctreeW (Indexed A) B X)
    (P : A → Prop) (a : A) (j : Nat) :
    ¬ entails (visWₜ (indexed_after P (j + 1))) t
      (.obs (E := writerE (Indexed A)) (stamp a j) ⟨⟩) := fun h => by
  cases h.1 with | obs _ _ h => exact absurd h.2 (Nat.not_succ_le_self j)

/-! ## Recurrence for repeating finite observation batches

`AF` by `u_iter_prefix_nat`, `AG AF` by coinduction over every finite suffix of a batch. -/

theorem emit_batches_af {B : Effect.{u}} (batch : I → List W) (next : I → I) (Inv : I → Prop)
    (rank : I → Nat) (P : W → Prop) (hnext : ∀ i, Inv i → Inv (next i))
    (hprogress : ∀ i, Inv i → (∃ o, o ∈ batch i ∧ P o) ∨ rank (next i) < rank i) :
    ∀ i w, Inv i → NotDone w →
      entails (AF (visWₜ P)) (emit_batches batch next i : ctreeW W B X) w := by
  intro i w hi hd
  refine u_iter_prefix_nat (q := .A) (fun j _ => Inv j) (fun j _ => rank j) hd hi
    fun j v hv hj => ?_
  rcases hprogress j hj with ⟨o, hin, hp⟩ | hlt
  · exact .inl (af_emit_list_member _ _ v P o hv hin hp)
  · exact .inr (af_emit_list_ret _ _ v _ hv
      ⟨next j, rfl, after_logs_not_done _ hv, hnext j hj, hlt⟩)

/-- Every remaining suffix of the current batch followed by the loop satisfies `AG AF`; each
coinductive step is guarded by a real log, from the suffix or the next nonempty batch. -/
theorem emit_batches_agaf {B : Effect.{u}} (batch : I → List W) (next : I → I) (Inv : I → Prop)
    (rank : I → Nat) (P : W → Prop) (hnext : ∀ i, Inv i → Inv (next i))
    (hnonempty : ∀ i, Inv i → batch i ≠ [])
    (hprogress : ∀ i, Inv i → (∃ o, o ∈ batch i ∧ P o) ∨ rank (next i) < rank i) :
    ∀ i w, Inv i → NotDone w →
      entails (AG (AF (visWₜ P))) (emit_batches batch next i : ctreeW W B X) w := by
  suffices H : ∀ j suffix (t : ctreeW W B X) v, Inv j → NotDone v →
      t ~ emit_list suffix (emit_batches batch next j) →
      entails (AG (AF (visWₜ P))) t v from
    fun i w hi hd => H i [] _ w hi hd (sbisim_refl _)
  coinduction R _ cih
  intro j suffix t v hj hv ht
  let L (j : I) : ctreeW W B X := emit_batches batch next j
  have haf : entails (AF (visWₜ P)) t v :=
    (proper_entails_meq _ ht).2 (af_emit_list _ _ v P hv
      (emit_batches_af batch next Inv rank P hnext hprogress j _ hj (after_logs_not_done _ hv)))
  obtain ⟨o, rest, j', hj', ht'⟩ : ∃ o rest j', Inv j' ∧ t ~ emit_list (o :: rest) (L j') := by
    cases suffix with
    | cons o rest => exact ⟨o, rest, j, hj, ht⟩
    | nil =>
      cases hb : batch j with
      | nil => exact absurd hb (hnonempty j hj)
      | cons o rest =>
        refine ⟨o, rest, next j, hnext j hj, sbisim_trans ht ?_⟩
        have := emit_batches_unfold_sbisim (B := B) (X := X) batch next j
        rwa [hb] at this
  refine ⟨haf, (proper_can_step ht').2 (can_step_log_bind o hv), fun t' w' tr => ?_⟩
  obtain ⟨u, tr, hu⟩ := ktrans_semiproper ht' tr
  rw [emit_list_cons] at tr
  obtain ⟨_, hw', rfl, -⟩ := ktrans_vis.1 tr
  exact cih j' rest t' w' hj' (hw' ▸ .obs _ _) hu

-- Not ported: nothing. Deviation: `EventuallyLabel`'s constructor premise is `¬ P l → …` instead
-- of Rocq's nested `P l ∨ …` (Lean rejects nested inductives through `Or` with bound variables);
-- `eventually_label_intro`/`eventually_label_ind` recover Rocq's constructor and eliminator.

end Tisl
