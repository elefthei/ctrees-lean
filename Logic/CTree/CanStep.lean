/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Trans
public import Logic.Interp.State

/-!
# Progress of ctrees

`can_step` on ctrees, by program structure: it ensures that universal modalities (`AN`, `AU`,
`AG`) are not trivially satisfied by a stuck tree. Also the native-return atom `ret` on ctrees,
which is exactly strong bisimilarity to `pure x` (← `CTree/Logic/CanStep.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinduction Notation
open ITree (Effect)
open Yield (br_alts)

section CanStepCtrees
variable {E B : Effect.{u}} {X Y : Type u} {w : World E}

/-- A hidden branch can step iff one of its branches can. -/
theorem can_step_br {c : B.I} {k : B.O c → CTree E B X} :
    can_step (CTree.br c k) w ↔ ∃ y, can_step (k y) w :=
  ⟨fun ⟨t', w', tr⟩ => let ⟨y, tr⟩ := ktrans_br.1 tr; ⟨y, t', w', tr⟩,
   fun ⟨y, t', w', tr⟩ => ⟨t', w', ktrans_br.2 ⟨y, tr⟩⟩⟩

theorem can_step_br_alts [Bn -< B] [LawfulSubeffect Bn B] {m : Nat}
    {k : Fin (m + 1) → CTree E B X} : can_step (br_alts m k) w ↔ ∃ a, can_step (k a) w :=
  ⟨fun ⟨t', w', tr⟩ => let ⟨a, tr⟩ := ktrans_br_alts.1 tr; ⟨a, t', w', tr⟩,
   fun ⟨a, t', w', tr⟩ => ⟨t', w', ktrans_br_alts.2 ⟨a, tr⟩⟩⟩

/-- A visible branch can step iff the world is not done. -/
theorem can_step_brS {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) :
    can_step (CTree.brS c k) w ↔ NotDone w :=
  ⟨can_step_not_done, fun hd => ⟨k y, w, ktrans_brS.2 ⟨y, rfl, rfl, hd⟩⟩⟩

/-- A visible step can step iff the world is not done. -/
theorem can_step_step {t : CTree E B X} : can_step (CTree.step t) w ↔ NotDone w :=
  ⟨can_step_not_done, fun hd => ⟨t, w, ktrans_step.2 ⟨rfl, rfl, hd⟩⟩⟩

/-- A guard can step iff the guarded tree can. -/
theorem can_step_guard {t : CTree E B X} : can_step (CTree.guard t) w ↔ can_step t w :=
  ⟨fun ⟨t', w', tr⟩ => ⟨t', w', ktrans_guard.1 tr⟩,
   fun ⟨t', w', tr⟩ => ⟨t', w', ktrans_guard.2 tr⟩⟩

/-- A visible event can step iff the world is not done. -/
theorem can_step_vis {e : E.I} {k : E.O e → CTree E B X} (v : E.O e) :
    can_step (CTree.vis e k) w ↔ NotDone w :=
  ⟨can_step_not_done, fun hd => ⟨k v, .obs e v, ktrans_vis.2 ⟨v, rfl, rfl, hd⟩⟩⟩

/-- A return can step from any non-done world. -/
theorem can_step_ret {x : X} (hd : NotDone w) : can_step (pure x : CTree E B X) w := by
  cases hd
  · exact ⟨_, _, ktrans_done.2 ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, ktrans_finish.2 ⟨rfl, rfl⟩⟩

/-- A stuck tree cannot step. -/
theorem can_step_stuck : ¬ can_step (.stuck : CTree E B X) w :=
  fun ⟨_, _, tr⟩ => ktrans_stuck tr

/-- A bind can step iff its prefix steps without terminating, or terminates and the
continuation can step. -/
theorem can_step_bind {t : CTree E B Y} {k : Y → CTree E B X} :
    can_step (t >>= k) w ↔
      (∃ t' w', ktrans t w t' w' ∧ NotDone w') ∨
        (∃ y w', ktrans t w .stuck w' ∧ done_eq y w' ∧ can_step (k y) w) := by
  constructor
  · rintro ⟨_, w', tr⟩
    rcases ktrans_bind_inv tr with ⟨t', tr, hd, -⟩ | ⟨y, w₀, tr, hd, trk⟩
    · exact .inl ⟨t', w', tr, hd⟩
    · exact .inr ⟨y, w₀, tr, hd, _, _, trk⟩
  · rintro (⟨t', w', tr, hd⟩ | ⟨y, w', tr, hd, u, w'', trk⟩)
    · exact ⟨_, w', ktrans_bind_l tr hd⟩
    · exact ⟨u, w'', ktrans_bind_r tr hd trk⟩

/-- A bind can step if its prefix steps without terminating. -/
theorem can_step_bind_l {t t' : CTree E B Y} {k : Y → CTree E B X} {w' : World E}
    (tr : ktrans t w t' w') (hd : NotDone w') : can_step (t >>= k) w :=
  can_step_bind.2 (.inl ⟨t', w', tr, hd⟩)

/-- A bind can step if its prefix eventually returns into states where the continuation can
step. -/
theorem can_step_bind_r {t : CTree E B Y} {k : Y → CTree E B X} {R : Y → World E → Prop}
    (hau : entails (AF (.ret R)) t w) (hk : ∀ y w, R y w → can_step (k y) w) :
    can_step (t >>= k) w := by
  refine can_step_bind.2 ?_
  rcases auc_unfold.1 hau with ⟨y, hR, -, ⟨t', w', tr⟩, hdone⟩ | ⟨-, ⟨t', w', tr⟩, hnext⟩
  · cases hdone t' w' tr with
    | pure =>
      obtain ⟨rfl, -⟩ := ktrans_to_done_inv tr
      exact .inr ⟨y, _, tr, .done y rfl, hk y _ hR⟩
    | obs e v =>
      obtain ⟨rfl, -⟩ := ktrans_to_finish_inv tr
      exact .inr ⟨y, _, tr, .finish e v y rfl, hk y _ hR⟩
  · have hd := ticl_not_done (AF (.ret R)) (hnext t' w' tr)
    exact .inl ⟨t', w', tr, hd⟩

/-- An iteration can step if its body can step without terminating. -/
theorem can_step_iter {I : Type u} {k : I → CTree E B (I ⊕ X)} {i : I} {t' : CTree E B (I ⊕ X)}
    {w' : World E} (tr : ktrans (k i) w t' w') (hd : NotDone w') :
    can_step (CTree.iter k i) w := by
  rw [unfold_iter]; exact can_step_bind_l tr hd

end CanStepCtrees

/-! ## `can_step` for state interpretations -/

section CanStepInterp
variable {E F B : Effect.{u}} {S : Type u} (h : (e : E.I) → StateT S (CTree F B) (E.O e))
  {X Y : Type u} {w : World F}

/-- A stateful bind can step if the interpreted prefix steps without terminating. -/
theorem can_step_state_bind_l {k : X → CTree E B Y} {s : S} {t : CTree E B X}
    {t' : CTree F B (X × S)} {w' : World F} (tr : ktrans (interp_state h t s) w t' w')
    (hd : NotDone w') : can_step (interp_state h (t >>= k) s) w := by
  rw [interp_state_bind]; exact can_step_bind_l tr hd

/-- A stateful bind can step if the interpreted prefix eventually returns `(x, s')` in `w'` and
the interpreted continuation can step from there. -/
theorem can_step_state_bind_r {k : X → CTree E B Y} {s s' : S} {t : CTree E B X} {x : X}
    {w' : World F} (hau : entails (AF (ret= (x, s') w')) (interp_state h t s) w)
    (hk : can_step (interp_state h (k x) s') w') : can_step (interp_state h (t >>= k) s) w := by
  rw [interp_state_bind]
  refine can_step_bind_r hau ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact hk

/-- A stateful iteration can step if its interpreted body can step without terminating. -/
theorem can_step_state_iter {I : Type u} {k : I → CTree E B (I ⊕ X)} {i : I} {s : S}
    {t' : CTree F B ((I ⊕ X) × S)} {w' : World F} (tr : ktrans (interp_state h (k i) s) w t' w')
    (hd : NotDone w') : can_step (interp_state h (CTree.iter k i) s) w := by
  rw [interp_state_unfold_iter]; exact can_step_bind_l tr hd

end CanStepInterp

/-! ## Logs -/

section CanStepLog
variable {S X : Type u} {B : Effect.{u}} {w : World (writerE S)}

/-- `log s` can step from any non-done world. -/
theorem can_step_log (s : S) (hd : NotDone w) : can_step (log s : CTree (writerE S) B PUnit) w :=
  (can_step_vis (E := writerE S) (⟨⟩ : PUnit)).2 hd

theorem can_step_log_bind (s : S) {t : ctreeW S B X} (hd : NotDone w) :
    can_step (log s >>= fun _ => t) w :=
  can_step_bind_l (ktrans_vis.2 ⟨(⟨⟩ : PUnit), rfl, rfl, hd⟩) (.obs (E := writerE S) s ⟨⟩)

end CanStepLog

/-- A bind cannot step when its prefix cannot. -/
theorem nostep_bind {E B : Effect.{u}} {X Y : Type u} {t : CTree E B Y} {k : Y → CTree E B X}
    {w : World E} (hns : ¬ can_step t w) : ¬ can_step (t >>= k) w := fun hs => by
  rcases can_step_bind.1 hs with ⟨t', w', tr, -⟩ | ⟨y, w', tr, -⟩
  · exact hns ⟨t', w', tr⟩
  · exact hns ⟨_, w', tr⟩

/-! ## The `ret` atom on ctrees

`entails (.ret R) t w` says every transition of `t` returns the same value `x` with `R x w`; on
ctrees this is exactly strong bisimilarity to `pure x`. -/

section CTreeRet
variable {E B : Effect.{u}} {X : Type u} {t : CTree E B X} {w : World E}

/-- Every transition of a tree whose world transitions all return `x` is the `val x` one. -/
private theorem trans_done_eq_inv {t' : CTree E B X} {x : X} {l : Label E} (hd : NotDone w)
    (htr : ∀ t' w', ktrans t w t' w' → done_eq x w') (tr : trans l t t') :
    l = .val x ∧ t' = .stuck := by
  cases l with
  | tau => have h := htr t' _ (Ktrans.tau hd tr); cases h <;> cases hd
  | obs e v => cases htr t' _ (Ktrans.obs e v hd tr)
  | val y =>
    cases trans_val_invT tr
    cases hd with
    | pure =>
      cases htr t' _ (Ktrans.done y tr) with
      | done _ h => subst h; exact ⟨rfl, trans_val_inv tr⟩
    | obs e v =>
      cases htr t' _ (Ktrans.finish e v y tr) with
      | finish _ _ _ h => subst h; exact ⟨rfl, trans_val_inv tr⟩

private theorem done_eq_of_done_of {x : X} {w' : World E} (h : DoneOf x w w') : done_eq x w' := by
  cases h
  · exact .done x rfl
  · exact .finish _ _ x rfl

theorem ret_sbisim {R : X → World E → Prop} (h : entails (.ret R) t w) :
    ∃ x, R x w ∧ t ~ (pure x : CTree E B X) := by
  obtain ⟨x, hR, hd, ⟨t₁, w₁, tr₁⟩, htr⟩ := h
  have htr' : ∀ t' w', ktrans t w t' w' → done_eq x w' := fun t' w' tr =>
    done_eq_of_done_of (htr t' w' tr)
  refine ⟨x, hR, sbisim_unfold.2 ⟨fun l t' tr => ?_, fun l u' tr => ?_⟩⟩
  · obtain ⟨rfl, rfl⟩ := trans_done_eq_inv hd htr' tr
    exact ⟨_, _, trans_ret x, sbisim_refl _, rfl⟩
  · obtain ⟨rfl, rfl⟩ := trans_ret_inv tr
    exact ⟨_, _, (ktrans_done_eq_inv tr₁ (htr' _ _ tr₁)).1, sbisim_refl _, rfl⟩

/-- `pure x` satisfies `ret R` in every non-done world where `R x` holds. -/
theorem ret_ret {x : X} {R : X → World E → Prop} (hd : NotDone w) (hR : R x w) :
    entails (.ret R) (pure x : CTree E B X) w := by
  refine ⟨x, hR, hd, can_step_ret hd, fun t' w' tr => ?_⟩
  cases hd
  · obtain ⟨rfl, -⟩ := ktrans_done.1 tr; exact .pure
  · obtain ⟨rfl, -⟩ := ktrans_finish.1 tr; exact .obs _ _

/-- `ret` is invariant under strong bisimulation, in particular under `guard`. -/
theorem ret_guard {R : X → World E → Prop} :
    entails (.ret R) (CTree.guard t) w ↔ entails (.ret R) t w :=
  proper_entails_meq (.ret R) (sb_guard t)

/-- A hidden branch whose branches all return exactly `x` returns `x`. -/
theorem ret_br {c : B.I} {k : B.O c → CTree E B X} (y : B.O c) {x : X} {R : X → World E → Prop}
    (hd : NotDone w) (hR : R x w) (hk : ∀ y, entails (ret= x w) (k y) w) :
    entails (.ret R) (CTree.br c k) w := by
  obtain ⟨_, -, -, hs, -⟩ := hk y
  refine ⟨x, hR, hd, can_step_br.2 ⟨y, hs⟩, fun t' w' tr => ?_⟩
  obtain ⟨y', tr⟩ := ktrans_br.1 tr
  obtain ⟨_, ⟨rfl, -⟩, -, -, htr⟩ := hk y'
  exact htr t' w' tr

end CTreeRet

-- Not ported: `proper_ctree_can_step` (`equ eq` is `=`).

end Tisl
