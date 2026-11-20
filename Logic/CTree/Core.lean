/- SPDX-License-Identifier: MIT -/
module

public import CTree
public import Logic.CTree.SBisimGrind

/-!
# TICL-side ctree core

Loop combinators, handler sums, iterated guards and the facts about silent divergence used by the
TICL ctree layer (← `CTree/Core.v`, `CTree/Events/State.v`).
-/

@[expose] public section
namespace Tisl
open CTree
open ITree (Effect)

variable {E F B : Effect.{u}} {X Y : Type u}

/-- Rocq `fin' n`. -/
abbrev fin' (n : Nat) := Fin (n + 1)

/-- Continue an `iter` loop (Rocq `continue`). -/
def continue_ : CTree E B (PUnit.{u + 1} ⊕ PUnit.{u + 1}) := pure (.inl ⟨⟩)
/-- Exit an `iter` loop (Rocq `break`). -/
def break_ : CTree E B (PUnit.{u + 1} ⊕ PUnit.{u + 1}) := pure (.inr ⟨⟩)

/-- Run `b i`, `b (i+1)`, … forever (Rocq `for i to ∞ b`). -/
def forever_from {E B : Effect.{0}} (b : Nat → CTree E B PUnit) (i : Nat) : CTree E B Nat :=
  CTree.forever (fun x => b x >>= fun _ => pure (x + 1)) i

/-- Repeat `b` until it breaks (Rocq `loop b`). -/
def loop (b : CTree E B (PUnit.{u + 1} ⊕ PUnit.{u + 1})) : CTree E B PUnit.{u + 1} :=
  CTree.iter (fun _ => b) ⟨⟩

/-- Case analysis on an event sum: a handler for `E1 ⊕ₑ E2` from handlers for each side. -/
def h_sum {E1 E2 : Effect.{u}} {M : Type u → Type v} (h1 : (e : E1.I) → M (E1.O e))
    (h2 : (e : E2.I) → M (E2.O e)) : (e : (E1 ⊕ₑ E2).I) → M ((E1 ⊕ₑ E2).O e)
  | .inl e => h1 e
  | .inr e => h2 e

/-- `n` administrative guards in front of `t`. -/
def guards : Nat → CTree E B X → CTree E B X
  | 0, t => t
  | n + 1, t => .guard (guards n t)

@[simp] theorem guards_zero (t : CTree E B X) : guards 0 t = t := rfl
@[simp] theorem guards_succ (n : Nat) (t : CTree E B X) :
    guards (n + 1) t = .guard (guards n t) := rfl

@[grind =] theorem bind_guards (n : Nat) (t : CTree E B X) (k : X → CTree E B Y) :
    (guards n t >>= k) = guards n (t >>= k) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

open Coinduction in
@[grind .] theorem guards_sbisim (n : Nat) (t : CTree E B X) : guards n t ~ t := by
  induction n with
  | zero => exact sbisim_refl t
  | succ n ih => exact sb_guard_l ih

@[grind =] theorem translate_guards (f : (e : E.I) → (e' : F.I) × (F.O e' → E.O e)) (k : Nat)
    (t : CTree E B X) : translate f (guards k t) = guards k (translate f t) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

/-- Pure silent divergence is preserved by sequencing. -/
theorem bind_spin (k : X → CTree E B Y) : ((CTree.spin : CTree E B X) >>= k) = CTree.spin :=
  spin_bind k

/-- Pure silent divergence is preserved by event relabelling. -/
theorem translate_spin (f : (e : E.I) → (e' : F.I) × (F.O e' → E.O e)) :
    translate f (CTree.spin : CTree E B X) = CTree.spin := by
  have h1 : (translate f (CTree.spin : CTree E B X)).unfold = .guard (translate f CTree.spin) := by
    conv => lhs; rw [unfold_spin]
    simp
  refine eq_coind (fun a b => a = translate f CTree.spin ∧ b = CTree.spin) ?_ _ _ ⟨rfl, rfl⟩
  rintro _ _ ⟨rfl, rfl⟩
  rw [h1, spin_unfold]
  exact .guard ⟨rfl, rfl⟩

/-- A tree equal to its own guard is pure silent divergence. -/
theorem guard_fixed_spin (t : CTree E B X) (h : t = .guard t) : t = CTree.spin := by
  refine eq_coind (fun a b => a = .guard a ∧ b = CTree.spin) ?_ _ _ ⟨h, rfl⟩
  rintro a _ ⟨ha, rfl⟩
  rw [ha, unfold_guard, spin_unfold]
  exact .guard ⟨ha, rfl⟩

-- Not ported: `guard_equ_node`, `vis_equ_node` (`congrArg` on equality); `desobs` (Ltac);
-- `put`/`get` (the ctrees `CTree.put`/`CTree.get` are used).

end Tisl
