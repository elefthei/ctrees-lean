/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Core
public import Logic.Utils.Vectors

/-!
# Scheduling policies and finite alternatives

Round-robin picks, the `Scheduler` record of scheduling policies, and `br_alts`, the hidden
branch over `m+1` alternatives used by both the scheduler and the TICL transition rules
(← first part of `CTree/Interp/Yield/Mod.v`; split off so that `Logic/CTree/Trans.lean` does not
depend on the scheduler).
-/

@[expose] public section
namespace Tisl.Yield
open CTree
open ITree (Effect)

/-- The round-robin choice among `n+1` slots at `cursor`. -/
def rr_pick (n cursor : Nat) : Fin (n + 1) := ⟨cursor % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- A singleton round-robin pool always picks its only slot. -/
theorem rr_pick_0 (m : Nat) : rr_pick 0 m = 0 := Fin.ext (Nat.mod_one m)

/-- Compare numeric choices, not the proof arguments of finite indices. -/
theorem rr_pick_mod_congr {n cursor cursor' : Nat} (h : cursor % (n + 1) = cursor' % (n + 1)) :
    rr_pick n cursor = rr_pick n cursor' := Fin.ext h

/-- Rocq `Nat.even n = true` is `n % 2 = 0`. -/
theorem rr_pick_even {n : Nat} (h : n % 2 = 0) : rr_pick 1 n = 0 := Fin.ext h

theorem rr_pick_odd {n : Nat} (h : n % 2 = 1) : rr_pick 1 n = 1 := Fin.ext h

/-- A scheduling policy: at a scheduling point of a pool of size `n+1` it offers
`sched_arity n st + 1` alternatives, each resolving to a slot and a successor state. -/
structure Scheduler : Type 1 where
  sched_state : Type
  sched_arity : Nat → sched_state → Nat
  sched_pick : (n : Nat) → (st : sched_state) → Fin (sched_arity n st + 1) →
    Fin (n + 1) × sched_state

/-- Round robin: no choice, the cursor advances. -/
def rr_scheduler : Scheduler where
  sched_state := Nat
  sched_arity _ _ := 0
  sched_pick n m _ := (rr_pick n m, m + 1)

/-- Nondeterministic selection: stateless, any slot. -/
def nd_scheduler : Scheduler where
  sched_state := PUnit
  sched_arity n _ := n
  sched_pick _ _ c := (c, ⟨⟩)

theorem slot_index_rr_pick (n cursor : Nat) : slot_index (rr_pick n cursor) = cursor % (n + 1) :=
  rfl

/-- Logged selections while an unfocused pool of returning slots shrinks. -/
def rr_return_picks : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, cursor => slot_index (rr_pick n cursor) :: rr_return_picks n (cursor + 1)

/-! ## Finite alternatives -/

variable {E F B : Effect.{u}} {X : Type u}

/-- `m+1` alternatives: a single one is taken directly, more are a hidden branch. -/
def br_alts [Bn -< B] : (m : Nat) → (Fin (m + 1) → CTree E B X) → CTree E B X
  | 0, k => k 0
  | m + 1, k => CTree.brn (m + 2) k

open Coinduction in
theorem br_alts_sbisim [Bn -< B] (m : Nat) {k k' : Fin (m + 1) → CTree E B X}
    (h : ∀ a, k a ~ k' a) : br_alts m k ~ br_alts m k' := by
  cases m with
  | zero => exact h 0
  | succ m => exact sb_br_id _ _ _ fun _ => h _

theorem trans_br_alts_inv [Bn -< B] (m : Nat) {k : Fin (m + 1) → CTree E B X} {l : Label E}
    {t' : CTree E B X} (h : trans l (br_alts m k) t') : ∃ a, trans l (k a) t' := by
  cases m with
  | zero => exact ⟨0, h⟩
  | succ m =>
    obtain ⟨n, h⟩ := trans_br'_inv (B₁ := Bn) (c := ⟨m + 2⟩) (k := fun x => k x.down) h
    exact ⟨_, h⟩

theorem trans_br_alts [Bn -< B] [LawfulSubeffect Bn B] (m : Nat) {k : Fin (m + 1) → CTree E B X}
    {l : Label E} (a : Fin (m + 1)) {t' : CTree E B X} (h : trans l (k a) t') :
    trans l (br_alts m k) t' := by
  cases m with
  | zero => rwa [fin1_eq a] at h
  | succ m => exact trans_br' (B₁ := Bn) (c := ⟨m + 2⟩) (k := fun x => k x.down) ⟨a⟩ h

open Coinduction in
/-- Interpreting a state handler through the alternatives. -/
theorem interp_state_br_alts_sb [Bn -< B] {S : Type u}
    (h : (e : E.I) → StateT S (CTree F B) (E.O e))
    (m : Nat) (k : Fin (m + 1) → CTree E B X) (s : S) :
    interp_state h (br_alts m k) s ~ br_alts m (fun a => interp_state h (k a) s) := by
  cases m with
  | zero => exact sbisim_refl _
  | succ m =>
    simp only [br_alts, CTree.brn, CTree.br', interp_state_br, CTree.branch', br_bind, pure_bind']
    exact sb_br_id _ _ _ fun _ => sb_guard_l (sbisim_refl _)

-- Not ported: `br_alts_equ` (`congrArg`).

end Tisl.Yield
