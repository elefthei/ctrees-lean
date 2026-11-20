/- SPDX-License-Identifier: MIT -/
module

public import Logic.Setoid
public import Logic.Yield.Scheduler

/-!
# The ctree Kripke structure

The Kripke transition system of ctrees, on top of the labelled transitions `trans`: a `tau` keeps
the world, `obs e v` records the observation, and `val x` finishes in `done x` (from `pure`) or
`finish e v x` (from `obs e v`). Hidden branches and guards are crawled through by `trans`
(← `CTree/Logic/Trans.v`).
-/

@[expose] public section
namespace Tisl
open CTree Coinduction
open ITree (Effect)
open Yield (br_alts)

variable {E B : Effect.{u}} {X Y : Type u}

/-- The world transitions of ctrees (Rocq `ktrans_`). -/
inductive Ktrans {X : Type u} : CTree E B X → World E → CTree E B X → World E → Prop
  | tau {t t' : CTree E B X} {w : World E} : NotDone w → trans .tau t t' → Ktrans t w t' w
  | obs {t t' : CTree E B X} {w : World E} (e : E.I) (v : E.O e) :
      NotDone w → trans (.obs e v) t t' → Ktrans t w t' (.obs e v)
  | done {t t' : CTree E B X} (x : X) : trans (.val x) t t' → Ktrans t .pure t' (.done x)
  | finish {t t' : CTree E B X} (e : E.I) (v : E.O e) (x : X) :
      trans (.val x) t t' → Ktrans t (.obs e v) t' (.finish e v x)

/-- `Ktrans` is a Kripke transition system for ctrees. -/
instance ctree_kripke : Kripke CTree E B where
  ktrans := Ktrans
  ktrans_not_done h := by cases h <;> first | assumption | constructor

variable {t t' u : CTree E B X} {w w' : World E}

/-- Characterization of `ktrans` in terms of the labelled `trans`. -/
theorem ktrans_trans :
    ktrans t w t' w' ↔
      ∃ l, trans l t t' ∧
        ((l = .tau ∧ NotDone w ∧ w' = w)
          ∨ (∃ (e : E.I) (x : E.O e), l = .obs e x ∧ NotDone w ∧ w' = .obs e x)
          ∨ (∃ x : X, l = .val x ∧ w = .pure ∧ t' = .stuck ∧ w' = .done x)
          ∨ (∃ (e : E.I) (v : E.O e) (x : X), l = .val x ∧ w = .obs e v ∧ t' = .stuck ∧
              w' = .finish e v x)) := by
  constructor
  · rintro (⟨hd, tr⟩ | ⟨e, v, hd, tr⟩ | ⟨x, tr⟩ | ⟨e, v, x, tr⟩)
    · exact ⟨_, tr, .inl ⟨rfl, hd, rfl⟩⟩
    · exact ⟨_, tr, .inr (.inl ⟨e, v, rfl, hd, rfl⟩)⟩
    · exact ⟨_, tr, .inr (.inr (.inl ⟨x, rfl, rfl, trans_val_inv tr, rfl⟩))⟩
    · exact ⟨_, tr, .inr (.inr (.inr ⟨e, v, x, rfl, rfl, trans_val_inv tr, rfl⟩))⟩
  · rintro ⟨l, tr, ⟨rfl, hd, rfl⟩ | ⟨e, x, rfl, hd, rfl⟩ | ⟨x, rfl, rfl, -, rfl⟩ |
      ⟨e, v, x, rfl, rfl, -, rfl⟩⟩
    · exact .tau hd tr
    · exact .obs e x hd tr
    · exact .done x tr
    · exact .finish e v x tr

/-- `ktrans` only depends on the labelled transitions of the source. -/
private theorem ktrans_of_trans {s : CTree E B X} (h : ∀ l, trans l t t' → trans l s t')
    (tr : ktrans t w t' w') : ktrans s w t' w' := by
  cases tr with
  | tau hd tr => exact .tau hd (h _ tr)
  | obs e v hd tr => exact .obs e v hd (h _ tr)
  | done x tr => exact .done x (h _ tr)
  | finish e v x tr => exact .finish e v x (h _ tr)

/-- `ktrans` crawls through `guard`. -/
theorem ktrans_guard : ktrans (.guard t) w t' w' ↔ ktrans t w t' w' :=
  ⟨ktrans_of_trans fun _ => trans_guard_inv, ktrans_of_trans fun _ => trans_guard⟩

/-- A hidden branch steps iff one of its branches steps. -/
theorem ktrans_br {c : B.I} {k : B.O c → CTree E B X} :
    ktrans (.br c k) w t w' ↔ ∃ i, ktrans (k i) w t w' := by
  constructor
  · intro tr
    rcases ktrans_trans.1 tr with ⟨l, tr, h⟩
    obtain ⟨i, tr⟩ := trans_br_inv tr
    exact ⟨i, ktrans_trans.2 ⟨l, tr, h⟩⟩
  · rintro ⟨i, tr⟩
    exact ktrans_of_trans (fun _ => trans_br i) tr

/-- A step of `br_alts` is a step of one alternative. -/
theorem ktrans_br_alts [Bn -< B] [LawfulSubeffect Bn B] {m : Nat}
    {k : Fin (m + 1) → CTree E B X} :
    ktrans (br_alts m k) w t w' ↔ ∃ a, ktrans (k a) w t w' := by
  constructor
  · intro tr
    rcases ktrans_trans.1 tr with ⟨l, tr, h⟩
    obtain ⟨a, tr⟩ := Yield.trans_br_alts_inv m tr
    exact ⟨a, ktrans_trans.2 ⟨l, tr, h⟩⟩
  · rintro ⟨a, tr⟩
    exact ktrans_of_trans (fun _ => Yield.trans_br_alts m a) tr

/-- `step t` is a single `tau` step. -/
theorem ktrans_step : ktrans (.step t) w t' w' ↔ t' = t ∧ w = w' ∧ NotDone w := by
  constructor
  · rintro (⟨hd, tr⟩ | ⟨_, _, _, tr⟩ | ⟨_, tr⟩ | ⟨_, _, _, tr⟩) <;>
      obtain ⟨h, hl⟩ := trans_step_inv tr <;> first | exact ⟨h, rfl, hd⟩ | cases hl
  · rintro ⟨rfl, rfl, hd⟩
    exact .tau hd (trans_step _)

/-- A visible branch is a single `tau` step choosing a branch. -/
theorem ktrans_brS {c : B.I} {k : B.O c → CTree E B X} :
    ktrans (.brS c k) w t w' ↔ ∃ i, t = k i ∧ w = w' ∧ NotDone w := by
  simp only [CTree.brS, ktrans_br (E := E), ktrans_step]

/-- `pure x` from `pure` is a single step to `done x`. -/
theorem ktrans_done {x : X} :
    ktrans (pure x : CTree E B X) .pure t w' ↔ w' = .done x ∧ t = .stuck := by
  constructor
  · intro h
    cases h with
    | tau _ tr => cases (trans_ret_inv tr).2
    | obs _ _ _ tr => cases (trans_ret_inv tr).2
    | done _ tr => obtain ⟨h, hl⟩ := trans_ret_inv tr; cases val_eq_inv hl; exact ⟨rfl, h⟩
  · rintro ⟨rfl, rfl⟩
    exact .done x (trans_ret x)

/-- `pure x` from `obs e v` is a single step to `finish e v x`. -/
theorem ktrans_finish {e : E.I} {v : E.O e} {x : X} :
    ktrans (pure x : CTree E B X) (.obs e v) t w' ↔ w' = .finish e v x ∧ t = .stuck := by
  constructor
  · intro h
    cases h with
    | tau _ tr => cases (trans_ret_inv tr).2
    | obs _ _ _ tr => cases (trans_ret_inv tr).2
    | finish _ _ _ tr => obtain ⟨h, hl⟩ := trans_ret_inv tr; cases val_eq_inv hl; exact ⟨rfl, h⟩
  · rintro ⟨rfl, rfl⟩
    exact .finish e v x (trans_ret x)

/-- `vis e k` is a single step observing `e`. -/
theorem ktrans_vis {e : E.I} {k : E.O e → CTree E B X} :
    ktrans (.vis e k) w t w' ↔ ∃ x, w' = .obs e x ∧ k x = t ∧ NotDone w := by
  constructor
  · rintro (⟨_, tr⟩ | ⟨_, _, hd, tr⟩ | ⟨_, tr⟩ | ⟨_, _, _, tr⟩) <;>
      obtain ⟨x, h, hl⟩ := trans_vis_inv tr <;> cases hl
    exact ⟨x, rfl, h.symm, hd⟩
  · rintro ⟨x, rfl, rfl, hd⟩
    exact .obs e x hd (trans_vis x k)

/-- Steps into `pure` start from `pure`. -/
theorem ktrans_pure_pred (h : ktrans t w t' .pure) : w = .pure := by
  cases h; rfl

/-- `stuck` does not step. -/
theorem ktrans_stuck : ¬ ktrans (.stuck : CTree E B X) w t w' := by
  rintro (⟨_, tr⟩ | ⟨_, _, _, tr⟩ | ⟨_, tr⟩ | ⟨_, _, _, tr⟩) <;> exact trans_stuck_inv tr

/-- Nothing steps from a done world. -/
theorem done_not_ktrans (hw : IsDone X w) : ¬ ∃ t' w', ktrans t w t' w' := by
  rintro ⟨_, _, tr⟩
  cases hw <;> cases ktrans_not_done tr

/-- Nothing steps from `done x`. -/
theorem ktrans_done_inv {x : X} : ¬ ktrans t (.done x) t' w := fun tr => by
  cases ktrans_not_done tr

/-- Nothing steps from `finish e v x`. -/
theorem ktrans_finish_inv {e : E.I} {v : E.O e} {x : X} : ¬ ktrans t (.finish e v x) t' w :=
  fun tr => by cases ktrans_not_done tr

theorem ktrans_to_done_inv {x : X} (h : ktrans t w t' (.done x)) : t' = .stuck ∧ w = .pure := by
  cases h with
  | tau hd => cases hd
  | done _ tr => exact ⟨trans_val_inv tr, rfl⟩

theorem ktrans_to_finish_inv {e : E.I} {v : E.O e} {x : X} (h : ktrans t w t' (.finish e v x)) :
    t' = .stuck ∧ w = .obs e v := by
  cases h with
  | tau hd => cases hd
  | finish _ _ _ tr => exact ⟨trans_val_inv tr, rfl⟩

/-- Any step to a terminal world returning `x` is the `val x` transition. -/
theorem ktrans_done_eq_inv {x : X} (h : ktrans t w t' w') (hd : done_eq x w') :
    trans (.val x) t .stuck ∧ NotDone w ∧ DoneOf x w w' := by
  cases hd with
  | done x' h' =>
    subst h'
    cases h with
    | tau hd => cases hd
    | done _ tr => exact ⟨trans_val_inv tr ▸ tr, .pure, .pure⟩
  | finish e v x' h' =>
    subst h'
    cases h with
    | tau hd => cases hd
    | finish _ _ _ tr => exact ⟨trans_val_inv tr ▸ tr, .obs e v, .obs e v⟩

variable {t₀ t₀' : CTree E B Y} {k : Y → CTree E B X}

/-- If `t` steps to `t'` without terminating, `t >>= k` steps to `t' >>= k`. -/
theorem ktrans_bind_l (h : ktrans t₀ w t₀' w') (hd : NotDone w') :
    ktrans (t₀ >>= k) w (t₀' >>= k) w' := by
  cases h with
  | tau hw tr => exact .tau hw (trans_bind_l isVal_tau tr)
  | obs e v hw tr => exact .obs e v hw (trans_bind_l isVal_obs tr)
  | done => cases hd
  | finish => cases hd

/-- If `t` returns `y` and `k y` steps, then `t >>= k` steps. -/
theorem ktrans_bind_r {y : Y} {w₀ : World E} (ht : ktrans t₀ w .stuck w₀) (hd : done_eq y w₀)
    (hk : ktrans (k y) w u w') : ktrans (t₀ >>= k) w u w' :=
  ktrans_of_trans (fun _ => trans_bind_r (ktrans_done_eq_inv ht hd).1) hk

theorem ktrans_bind_inv (h : ktrans (t₀ >>= k) w u w') :
    (∃ t', ktrans t₀ w t' w' ∧ NotDone w' ∧ u = t' >>= k) ∨
      (∃ y w₀, ktrans t₀ w .stuck w₀ ∧ done_eq y w₀ ∧ ktrans (k y) w u w') := by
  rcases ktrans_trans.1 h with ⟨l, tr, hl⟩
  rcases trans_bind_inv tr with ⟨hv, t', tr', rfl⟩ | ⟨y, trv, trk⟩
  · left
    rcases hl with ⟨rfl, hw, rfl⟩ | ⟨e, x, rfl, hw, rfl⟩ | ⟨x, rfl, -⟩ | ⟨e, v, x, rfl, -⟩
    · exact ⟨t', .tau hw tr', hw, rfl⟩
    · exact ⟨t', .obs e x hw tr', .obs e x, rfl⟩
    · exact absurd (.val x) hv
    · exact absurd (.val x) hv
  · right
    have hk : ktrans (k y) w u w' := ktrans_trans.2 ⟨l, trk, hl⟩
    cases hw : ktrans_not_done h with
    | pure => exact ⟨y, _, .done y trv, .done y rfl, hk⟩
    | obs e v => exact ⟨y, _, .finish e v y trv, .finish e v y rfl, hk⟩

/-- `ktrans_semiproper` for strong bisimilarity. -/
private theorem ktrans_sbisim {s s' : CTree E B X} (hsb : s ~ t) (tr : ktrans s w s' w') :
    ∃ t', ktrans t w t' w' ∧ s' ~ t' := by
  have hf := (sbisim_unfold.1 hsb).1
  cases tr with
  | tau hd tr =>
    obtain ⟨_, t', tr', h, rfl⟩ := hf _ _ tr
    exact ⟨t', .tau hd tr', h⟩
  | obs e v hd tr =>
    obtain ⟨_, t', tr', h, rfl⟩ := hf _ _ tr
    exact ⟨t', .obs e v hd tr', h⟩
  | done x tr =>
    obtain ⟨_, t', tr', h, rfl⟩ := hf _ _ tr
    exact ⟨t', .done x tr', h⟩
  | finish e v x tr =>
    obtain ⟨_, t', tr', h, rfl⟩ := hf _ _ tr
    exact ⟨t', .finish e v x tr', h⟩

/-- Strong bisimilarity is a Kripke setoid: bisimilar trees match every world transition. -/
instance KripkeSetoidSBisim : KripkeSetoid CTree E B X (sbisim Eq) where
  equiv := sbisim_equivalence ⟨fun _ => rfl, .symm, .trans⟩
  ktrans_semiproper := ktrans_sbisim

/-- `P` respects strong bisimulation in its tree argument
(Rocq `Proper (sbisim eq ==> eq ==> iff) P`). -/
abbrev SbProper (P : CTree E B X → World E → Prop) : Prop :=
  ∀ {t u : CTree E B X} w, t ~ u → (P t w ↔ P u w)

/-- A tree bisimilar to `pure x` behaves like a return in a bind. -/
theorem ktrans_sbisim_ret {x : Y} (hsb : t₀ ~ (pure x : CTree E B Y))
    (h : ktrans (t₀ >>= k) w u w') : ktrans (k x) w u w' := by
  have hf := (sbisim_unfold.1 hsb).1
  rcases ktrans_bind_inv h with ⟨t', tr, hd, -⟩ | ⟨y, w₀, tr, hd, hk⟩
  · rcases ktrans_trans.1 tr with ⟨l, tr, hl⟩
    obtain ⟨_, _, tr', -, rfl⟩ := hf _ _ tr
    obtain ⟨-, rfl⟩ := trans_ret_inv tr'
    rcases hl with ⟨h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, -, -, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
    · cases h
    · cases h
    · cases hd
    · cases hd
  · obtain ⟨_, _, tr', -, rfl⟩ := hf _ _ (ktrans_done_eq_inv tr hd).1
    obtain ⟨-, h⟩ := trans_ret_inv tr'
    cases val_eq_inv h
    exact hk

-- Not ported: `ktrans_equ_proper` and `KripkeSetoidEqu` (`equ eq` is `=`); the `Hint Extern`
-- instance-resolution hints (Lean infers `CTree` from the tree's type).

end Tisl
