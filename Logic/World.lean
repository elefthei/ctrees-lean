/- SPDX-License-Identifier: MIT -/
module

public import ITree.Effect

/-!
# Kripke worlds

The worlds of the TICL Kripke models: no observation yet (`pure`), a visible event with its answer
(`obs`), and the two terminal worlds reached by returning a value (`done`, `finish`)
(← `Logic/World.v`).
-/

@[expose] public section
namespace Tisl
open ITree (Effect)

variable {E : Effect.{u}}

/-- Kripke worlds over the event signature `E`. -/
inductive World (E : Effect.{u}) : Type (u + 1)
  | pure
  | obs (e : E.I) (v : E.O e)
  | done {X : Type u} (x : X)
  | finish {X : Type u} (e : E.I) (v : E.O e) (x : X)

/-- Worlds that carry an observation. -/
inductive NotPure : World E → Prop
  | obs (e : E.I) (v : E.O e) : NotPure (.obs e v)
  | finish {X : Type u} (e : E.I) (v : E.O e) (x : X) : NotPure (.finish e v x)

/-- Worlds without an observation. -/
inductive IsPure : World E → Prop
  | pure : IsPure .pure
  | done {X : Type u} (x : X) : IsPure (.done x)

/-- Observation worlds whose event and answer satisfy `R`. -/
inductive VisWith (R : (e : E.I) → E.O e → Prop) : World E → Prop
  | obs (e : E.I) (v : E.O e) : R e v → VisWith R (.obs e v)

/-- Terminal worlds whose value and predecessor world satisfy `R`. -/
inductive DoneWith {X : Type u} (R : X → World E → Prop) : World E → Prop
  | done (x : X) : R x .pure → DoneWith R (.done x)
  | finish (e : E.I) (v : E.O e) (x : X) : R x (.obs e v) → DoneWith R (.finish e v x)

/-- Terminal postconditions are covariant without changing their predecessor world. -/
theorem done_with_mono {X : Type u} {P Q : X → World E → Prop} (hPQ : ∀ x w, P x w → Q x w)
    {wd : World E} (h : DoneWith P wd) : DoneWith Q wd := by
  cases h <;> constructor <;> apply hPQ <;> assumption

/-- Terminal worlds returning exactly `x`. -/
def done_eq {X : Type u} (x : X) : World E → Prop := DoneWith fun x' (_ : World E) => x = x'

/-- `DoneOf x w wd`: returning `x` from world `w` reaches the terminal world `wd`. -/
inductive DoneOf {X : Type u} (x : X) : World E → World E → Prop
  | pure : DoneOf x .pure (.done x)
  | obs (e : E.I) (v : E.O e) : DoneOf x (.obs e v) (.finish e v x)

theorem done_of_eq {X : Type u} (x : X) (w wd : World E) :
    DoneOf x w wd ↔ DoneWith (fun x' w' => x = x' ∧ w = w') wd := by
  constructor
  · rintro (_ | _) <;> constructor <;> exact ⟨rfl, rfl⟩
  · rintro (_ | _) <;> rename_i h <;> obtain ⟨rfl, rfl⟩ := h <;> constructor

/-- Non-terminal worlds. -/
inductive NotDone : World E → Prop
  | pure : NotDone .pure
  | obs (e : E.I) (v : E.O e) : NotDone (.obs e v)

/-- Terminal worlds returning a value of type `X`. -/
inductive IsDone (X : Type u) : World E → Prop
  | done (x : X) : IsDone X (.done x)
  | finish (e : E.I) (v : E.O e) (x : X) : IsDone X (.finish e v x)

@[simp] theorem notDone_pure : NotDone (.pure : World E) := .pure
@[simp] theorem notDone_obs (e : E.I) (v : E.O e) : NotDone (.obs e v) := .obs e v
@[simp] theorem not_notDone_done {X : Type u} (x : X) : ¬ NotDone (.done x : World E) := nofun
@[simp] theorem not_notDone_finish {X : Type u} (e : E.I) (v : E.O e) (x : X) :
    ¬ NotDone (.finish e v x) := nofun
@[simp] theorem isPure_pure : IsPure (.pure : World E) := .pure
@[simp] theorem isPure_done {X : Type u} (x : X) : IsPure (.done x : World E) := .done x
@[simp] theorem not_isPure_obs (e : E.I) (v : E.O e) : ¬ IsPure (.obs e v) := nofun
@[simp] theorem not_isPure_finish {X : Type u} (e : E.I) (v : E.O e) (x : X) :
    ¬ IsPure (.finish e v x) := nofun
@[simp] theorem notPure_obs (e : E.I) (v : E.O e) : NotPure (.obs e v) := .obs e v
@[simp] theorem notPure_finish {X : Type u} (e : E.I) (v : E.O e) (x : X) :
    NotPure (.finish e v x) := .finish e v x
@[simp] theorem not_notPure_pure : ¬ NotPure (.pure : World E) := nofun
@[simp] theorem not_notPure_done {X : Type u} (x : X) : ¬ NotPure (.done x : World E) := nofun
@[simp] theorem visWith_obs {R : (e : E.I) → E.O e → Prop} {e : E.I} {v : E.O e} :
    VisWith R (.obs e v) ↔ R e v := ⟨fun | .obs _ _ h => h, .obs e v⟩
@[simp] theorem not_visWith_pure {R : (e : E.I) → E.O e → Prop} : ¬ VisWith R (.pure : World E) :=
  nofun
@[simp] theorem not_visWith_done {R : (e : E.I) → E.O e → Prop} {X : Type u} (x : X) :
    ¬ VisWith R (.done x : World E) := nofun
@[simp] theorem not_visWith_finish {R : (e : E.I) → E.O e → Prop} {X : Type u} (e : E.I)
    (v : E.O e) (x : X) : ¬ VisWith R (.finish e v x) := nofun

theorem not_done_dec (w : World E) : NotDone w ∨ ∃ X, IsDone X w := by
  cases w with
  | pure => exact .inl .pure
  | obs e v => exact .inl (.obs e v)
  | done x => exact .inr ⟨_, .done x⟩
  | finish e v x => exact .inr ⟨_, .finish e v x⟩

theorem not_pure_dec (w : World E) : NotPure w ∨ IsPure w := by
  cases w with
  | pure => exact .inr .pure
  | obs e v => exact .inl (.obs e v)
  | done x => exact .inr (.done x)
  | finish e v x => exact .inl (.finish e v x)

instance : DecidablePred (NotDone (E := E))
  | .pure => isTrue .pure
  | .obs e v => isTrue (.obs e v)
  | .done _ => isFalse nofun
  | .finish .. => isFalse nofun

instance : DecidablePred (NotPure (E := E))
  | .pure => isFalse nofun
  | .obs e v => isTrue (.obs e v)
  | .done _ => isFalse nofun
  | .finish e v x => isTrue (.finish e v x)

end Tisl
