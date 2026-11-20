/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Core
public import Logic.Events.Writer

/-!
# Interpreting state events

TICL-specific equations for the ctrees state interpreter `interp_state` (whose structural
equations come from `CTree.Interp.FoldStateT`): the instrumented state handler `h_stateW`,
iteration under `interp_state`, and indexed emissions (← `CTree/Interp/State/Mod.v`).
Lean's `StateT` returns `(value, state)`; Rocq's returns `(state, value)`.
-/

@[expose] public section
namespace Tisl
open CTree Coinduction
open ITree (Effect)

/-- Interpret `stateE S` events into the writer monad with ghost state `S`. -/
def instr_stateE {S : Type u} {B : Effect.{u}} {X : Type u} (t : CTree (stateE S) B X) (σ : S) :
    ctreeW S B (X × S) :=
  interp_state h_stateW t σ

section InterpStateTicl
variable {E F B : Effect.{u}} {W : Type u} (h : (e : E.I) → StateT W (CTree F B) (E.O e))

/-- A trigger's administrative guard disappears under strong bisimulation. -/
@[grind .] theorem interp_state_trigger_bind {X : Type u} (e : E.I)
    (k : E.O e × W → CTree F B X) (s : W) :
    (interp_state h (CTree.trigger e : CTree E B (E.O e)) s >>= k) ~ (h e s >>= k) := by
  rw [interp_state_trigger, bind_assoc]
  exact sbisim_bind_eq _ fun _ => by rw [guard_bind, pure_bind']; exact sb_guard _

/-- `interp_state` of an iteration unfolds the loop and commutes the interpretation inside. -/
theorem interp_state_unfold_iter {I R : Type u} (k : I → CTree E B (I ⊕ R)) (i : I) (s : W) :
    interp_state h (CTree.iter k i) s = interp_state h (k i) s >>= fun
      | (.inl l, s) => .guard (interp_state h (CTree.iter k l) s)
      | (.inr r, s) => pure (r, s) := by
  rw [unfold_iter, interp_state_bind]
  congr 1; funext ⟨x, s'⟩
  cases x <;> simp

/-- A visible branch interprets to a visible branch, up to administrative guards. -/
theorem interp_state_brS {X : Type u} (c : B.I) (k : B.O c → CTree E B X) (s : W) :
    interp_state h (.brS c k) s ~ .brS c fun y => interp_state h (k y) s := by
  simp only [brS_eq, interp_state_br, CTree.branch', CTree.br', br_bind, pure_bind',
    interp_state_step]
  exact sb_br_id _ _ _ fun _ => sb_guard_l (sb_step (sb_guard _))

end InterpStateTicl

/-- `get` returns the state silently. -/
theorem interp_state_get {S : Type u} {B : Effect.{u}} (s : S) :
    interp_state (h_stateW (B := B)) (CTree.get : CTree (stateE S) B S) s ~
      (pure (s, s) : ctreeW S B (S × S)) := by
  show interp_state _ (CTree.trigger (E := stateE S) StateOp.get) s ~ _
  erw [interp_state_trigger]
  simp only [h_stateW, pure_bind']
  exact sb_guard _

/-- `put s'` logs `s'` and returns `(⟨⟩, s')`. -/
theorem interp_state_put {S : Type u} {B : Effect.{u}} (s s' : S) :
    interp_state (h_stateW (B := B)) (CTree.put s' : CTree (stateE S) B PUnit) s ~
      (log s' >>= fun _ => pure (⟨⟩, s') : ctreeW S B (PUnit × S)) := by
  show interp_state _ (CTree.trigger (E := stateE S) (StateOp.put s')) s ~ _
  erw [interp_state_trigger]
  simp only [h_stateW, log, vis_bind, pure_bind']
  exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

/-- `instr_stateE` of an iteration unfolds the loop and interprets the body. -/
theorem instr_state_unfold_iter {S : Type u} {B : Effect.{u}} {I R : Type u}
    (k : I → CTree (stateE S) B (I ⊕ R)) (i : I) (s : S) :
    instr_stateE (CTree.iter k i) s = instr_stateE (k i) s >>= fun
      | (.inl l, s) => .guard (instr_stateE (CTree.iter k l) s)
      | (.inr r, s) => pure (r, s) :=
  interp_state_unfold_iter _ k i s

/-- Interpreting one indexed emission: `h_indexed` leaves exactly one observation and advances the
shared occurrence counter once; the auxiliary state and the other handler are arbitrary. -/
theorem interp_indexed_emit {A Sg : Type u} {E B : Effect.{u}} {X : Type u}
    (other : (e : E.I) → StateT (Sg × Nat) (ctreeW (Indexed A) B) (E.O e))
    (a : A) (s : Sg) (c : Nat) (k : PUnit → CTree (E ⊕ₑ writerE A) B X) :
    interp_state (h_sum other h_indexed)
      ((CTree.trigger (E := E ⊕ₑ writerE A) (.inr a) : CTree (E ⊕ₑ writerE A) B PUnit) >>= k)
      (s, c) ~
    (log (stamp a c) >>= fun _ => interp_state (h_sum other h_indexed) (k ⟨⟩) (s, c + 1)) := by
  rw [interp_state_bind, interp_state_trigger]
  simp only [h_sum, h_indexed, log, vis_bind, pure_bind', guard_bind]
  exact sbisim_vis_id _ _ _ fun _ => ⟨sb_guard _, rfl⟩

end Tisl
