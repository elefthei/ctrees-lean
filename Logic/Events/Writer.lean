/- SPDX-License-Identifier: MIT -/
module

public import CTree

/-!
# Writer events and instrumentation

The writer effect `writerE S` (one deterministic event per logged value), indexed observations,
and the instrumentation handlers that leave a log event behind after a semantic step
(← `Events/WriterE.v`, `CTree/Events/Writer.v`).
-/

@[expose] public section
namespace Tisl
open CTree
open ITree (Effect)

/-- The empty effect (ITree's `void1`). -/
@[implicit_reducible] def void1 : Effect.{u} := ⟨PEmpty, fun e => e.elim⟩

/-- Writer events over ghost state `S`: the event `s` logs `s` and answers `⟨⟩`
(Rocq `Log s : writerE S unit`). -/
@[implicit_reducible] def writerE (S : Type u) : Effect.{u} := ⟨S, fun _ => PUnit⟩
unif_hint (S : Type u) (s : (writerE S).I) where |- (writerE S).O s ≟ PUnit.{u + 1}

/-- A payload together with the number of observations that preceded it (Rocq `indexed`). -/
structure Indexed (A : Type u) where
  value : A
  index : Nat

/-- Rocq `stamp`. -/
abbrev stamp {A : Type u} (a : A) (i : Nat) : Indexed A := ⟨a, i⟩

/-- `P` holds of the payload and the occurrence is not older than `lower`. -/
def indexed_after {A : Type u} (P : A → Prop) (lower : Nat) (o : Indexed A) : Prop :=
  P o.value ∧ lower ≤ o.index

/-- Log `s`. -/
def log {S : Type u} {B : Effect.{u}} (s : S) : CTree (writerE S) B PUnit :=
  .vis (E := writerE S) s fun _ => pure ⟨⟩

abbrev ctreeW (W : Type u) (B : Effect.{u}) := CTree (writerE W) B
abbrev InstrM (W : Type u) (B : Effect.{u}) (St : Type u) := StateT St (ctreeW W B)

theorem log_vis {W : Type u} {B : Effect.{u}} {X : Type u} (o : W) (t : ctreeW W B X) :
    (log o >>= fun _ => t) = .vis (E := writerE W) o fun _ => t := by
  simp [log]

variable {E B : Effect.{u}} {W St : Type u}

/-- Instrument a semantic handler `h` with an observation function: after each event, log the
observation if there is one. -/
def h_instr (h : (e : E.I) → StateT St (CTree void1 B) (E.O e))
    (obs : (e : E.I) → E.O e → St → Option W) : (e : E.I) → InstrM W B St (E.O e) :=
  fun e s =>
    translate (fun e => (e : PEmpty).elim) (h e s) >>= fun p =>
      match obs e p.1 p.2 with
      | some w => .vis (E := writerE W) w fun _ => pure p
      | none => pure p

/-- The instrumented state handler: logs after each `put`, not on `get`. -/
def h_stateW {S : Type u} : (e : (stateE S).I) → InstrM S B S ((stateE S).O e)
  | .get => fun s => pure (s, s)
  | .put s' => fun _ => log s' >>= fun _ => pure (⟨⟩, s')

/-- The shared indexing handler: every log emits one indexed observation and increments the
counter; the auxiliary state is passed through. -/
def h_indexed {A Sg : Type u} :
    (e : (writerE A).I) → StateT (Sg × Nat) (ctreeW (Indexed A) B) ((writerE A).O e) :=
  fun a sc => log (stamp a sc.2) >>= fun _ => pure (⟨⟩, (sc.1, sc.2 + 1))

theorem h_indexed_log {A Sg : Type u} (a : A) (s : Sg) (c : Nat) :
    h_indexed (B := B) (Sg := Sg) a (s, c) = (log (stamp a c) >>= fun _ => pure (⟨⟩, (s, c + 1))) :=
  rfl

end Tisl
