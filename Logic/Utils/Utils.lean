/- SPDX-License-Identifier: MIT -/
module

/-!
# Generic utilities

Small logical and `Option` facts plus a comparison on `Fin` (← `Utils/Utils.v`).
-/

@[expose] public section
namespace Tisl

theorem option_map_none {X Y} (f : X → Y) (m : Option X) : m.map f = none ↔ m = none := by
  cases m <;> simp

theorem option_map_some {X Y} (f : X → Y) (m : Option X) (v : Y) :
    m.map f = some v ↔ ∃ x, m = some x ∧ v = f x := by
  cases m <;> simp [eq_comm]

theorem pull2_iff {A B C} (P : A → B → Prop) (R : A → B → C → Prop) :
    (∀ a b, (∃ c, R a b c) → P a b) ↔ (∀ a b c, R a b c → P a b) :=
  ⟨fun h a b c hr => h a b ⟨c, hr⟩, fun h a b ⟨c, hr⟩ => h a b c hr⟩

/-- Exactly one of `A` and `B` holds. -/
def Disjoint (A B : Prop) : Prop := (A ∧ ¬B) ∨ (¬A ∧ B)

/-- Compare two `Fin`s of possibly different bounds; equal positions compare their remaining
bounds (Rocq recursion on `Fin.t` kept literally). -/
def Fin_compare : {m n : Nat} → Fin m → Fin n → Ordering
  | m + 1, n + 1, ⟨0, _⟩, ⟨0, _⟩ => compare m n
  | _ + 1, _ + 1, ⟨_ + 1, _⟩, ⟨0, _⟩ => .gt
  | _ + 1, _ + 1, ⟨0, _⟩, ⟨_ + 1, _⟩ => .lt
  | m + 1, n + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩ =>
    Fin_compare (m := m) (n := n) ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ⟨j, Nat.lt_of_succ_lt_succ hj⟩

end Tisl

-- Not ported: `is_true` coercion (core `Bool → Prop` coercion); `RelDecidable`, `EqDecidable`
-- (use `DecidableRel`/`DecidableEq`); tactics `ddestruction`, `split2`, `inv`, `hinduction`.
