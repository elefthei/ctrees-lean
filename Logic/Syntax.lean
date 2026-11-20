/- SPDX-License-Identifier: MIT -/
module

public import Logic.Kripke
public import Logic.Events.Writer

/-!
# TICL syntax

Formulas are indexed by `Option (Type u)`: `none` for prefix properties, `some X` for formulas
ending in a postcondition on a returned value of type `X`. Temporal guards are always prefix
properties (← `Logic/Syntax.v`).
-/

@[expose] public section
namespace Tisl
open ITree (Effect)

/-- Path quantifiers. -/
inductive Ticlq
  | A
  | E
  deriving DecidableEq

/-- Indexed TICL formulas. -/
inductive Ticl (E : Effect.{u}) : Option (Type u) → Type (u + 1)
  | now (p : World E → Prop) : Ticl E none
  | ret {X : Type u} (p : X → World E → Prop) : Ticl E (some X)
  | cu {i : Option (Type u)} (q : Ticlq) (p : Ticl E none) (r : Ticl E i) : Ticl E i
  | cx {i : Option (Type u)} (q : Ticlq) (p : Ticl E none) (r : Ticl E i) : Ticl E i
  | cg (q : Ticlq) (p : Ticl E none) : Ticl E none
  | and {i : Option (Type u)} (p r : Ticl E i) : Ticl E i
  | or {i : Option (Type u)} (p r : Ticl E i) : Ticl E i

/-- Prefix formulas (Rocq `ticll`). -/
abbrev TiclL (E : Effect.{u}) := Ticl E none
/-- Formulas with a postcondition on a returned `X` (Rocq `ticlr`). -/
abbrev TiclR (E : Effect.{u}) (X : Type u) := Ticl E (some X)
/-- Rocq `ticl_at E X b`. -/
abbrev TiclAt (E : Effect.{u}) (X : Type u) (b : Bool) := Ticl E (if b then some X else none)

variable {E : Effect.{u}} {X Y : Type u}

/-- Auxiliary for `map_ret`: the index is a variable so that structural recursion applies. -/
def mapRetAux (f : (X → World E → Prop) → Y → World E → Prop) :
    {i : Option (Type u)} → Ticl E i → i = some X → TiclR E Y
  | _, .ret p, h => match X, f, h with | _, f, rfl => .ret (f p)
  | _, .cu q p r, h => .cu q p (mapRetAux f r h)
  | _, .cx q p r, h => .cx q p (mapRetAux f r h)
  | _, .and p r, h => .and (mapRetAux f p h) (mapRetAux f r h)
  | _, .or p r, h => .or (mapRetAux f p h) (mapRetAux f r h)

/-- Map the return predicates of a formula; prefix guards are unchanged. -/
def map_ret (f : (X → World E → Prop) → Y → World E → Prop) (p : TiclR E X) : TiclR E Y :=
  mapRetAux f p rfl

section MapRet
variable (f : (X → World E → Prop) → Y → World E → Prop)
@[simp] theorem map_ret_ret (p : X → World E → Prop) : map_ret f (.ret p) = .ret (f p) := rfl
@[simp] theorem map_ret_cu (q : Ticlq) (p : TiclL E) (r : TiclR E X) :
    map_ret f (.cu q p r) = .cu q p (map_ret f r) := rfl
@[simp] theorem map_ret_cx (q : Ticlq) (p : TiclL E) (r : TiclR E X) :
    map_ret f (.cx q p r) = .cx q p (map_ret f r) := rfl
@[simp] theorem map_ret_and (p r : TiclR E X) :
    map_ret f (.and p r) = .and (map_ret f p) (map_ret f r) := rfl
@[simp] theorem map_ret_or (p r : TiclR E X) :
    map_ret f (.or p r) = .or (map_ret f p) (map_ret f r) := rfl
end MapRet

/-- Auxiliary for `map_atoms`: return atoms are known to have type `X`. -/
def mapAtomsAux (now_map : (World E → Prop) → World E → Prop)
    (ret_map : (X → World E → Prop) → X → World E → Prop) :
    {i : Option (Type u)} → Ticl E i → (∀ Y, i = some Y → Y = X) → Ticl E i
  | _, .now p, _ => .now (now_map p)
  | _, .ret (X := Y) p, h => match Y, p, h Y rfl with | _, p, rfl => .ret (ret_map p)
  | _, .cu q p r, h => .cu q (mapAtomsAux now_map ret_map p nofun) (mapAtomsAux now_map ret_map r h)
  | _, .cx q p r, h => .cx q (mapAtomsAux now_map ret_map p nofun) (mapAtomsAux now_map ret_map r h)
  | _, .cg q p, _ => .cg q (mapAtomsAux now_map ret_map p nofun)
  | _, .and p r, h => .and (mapAtomsAux now_map ret_map p h) (mapAtomsAux now_map ret_map r h)
  | _, .or p r, h => .or (mapAtomsAux now_map ret_map p h) (mapAtomsAux now_map ret_map r h)

theorem ticlAt_ret_type (b : Bool) : ∀ Y, (if b then some X else none) = some Y → Y = X := by
  cases b <;> simp

/-- Transform every atom, including prefix guards, without changing indices. -/
def map_atoms (now_map : (World E → Prop) → World E → Prop)
    (ret_map : (X → World E → Prop) → X → World E → Prop) (b : Bool) (p : TiclAt E X b) :
    TiclAt E X b :=
  mapAtomsAux now_map ret_map p (ticlAt_ret_type b)

/-- Precompose the return predicates with `f`. -/
def contramap (f : Y → X) : TiclR E X → TiclR E Y := map_ret fun p y w => p (f y) w

/-- Observation worlds of a log event whose payload satisfies `R` (the atom of Rocq `visW R`). -/
abbrev visW {S : Type u} (R : S → Prop) : World (writerE S) → Prop := VisWith fun s _ => R s

/-! ## Notation -/

namespace Notation
scoped notation "⊤" => Ticl.now fun _ => True
scoped notation "⊥" => Ticl.now fun _ => False
/-- Rocq `pure`. -/
scoped notation "pureₜ" => Ticl.now (· = World.pure)
/-- Rocq `vis R`. -/
scoped notation:max "visₜ " R:max => Ticl.now (VisWith R)
/-- Rocq `visW R`, for `E = writerE S` and `R : S → Prop`. -/
scoped notation:max "visWₜ " R:max => Ticl.now (visW R)
/-- Rocq `ret= r w`. -/
scoped notation:max "ret= " r:max w:max => Ticl.ret fun r' w' => r = r' ∧ w = w'
scoped infixr:60 " AN " => Ticl.cx Ticlq.A
scoped infixr:60 " EN " => Ticl.cx Ticlq.E
scoped infixr:60 " AU " => Ticl.cu Ticlq.A
scoped infixr:60 " EU " => Ticl.cu Ticlq.E
scoped prefix:70 "AG " => Ticl.cg Ticlq.A
scoped prefix:70 "EG " => Ticl.cg Ticlq.E
scoped notation:70 "AF " φ:70 => Ticl.cu Ticlq.A (Ticl.now fun _ => True) φ
scoped notation:70 "EF " φ:70 => Ticl.cu Ticlq.E (Ticl.now fun _ => True) φ
scoped notation:70 "AX " φ:70 => Ticl.cx Ticlq.A (Ticl.now fun _ => True) φ
scoped notation:70 "EX " φ:70 => Ticl.cx Ticlq.E (Ticl.now fun _ => True) φ
scoped infixl:35 " ∧ₜ " => Ticl.and
scoped infixl:35 " ∨ₜ " => Ticl.or
end Notation

-- Not ported: `ticl_at_ind`, `ticll_ind` (Equations induction principles; `induction φ` on the
-- indexed `Ticl` replaces them).

end Tisl
