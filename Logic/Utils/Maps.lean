/- SPDX-License-Identifier: MIT -/
module

/-!
# String-keyed contexts

Association lists from variable names to naturals with ExtLib `alist` semantics (`add` removes the
old binding, then conses the new one), and the `assert1`/`assert2` lookup predicates
(← `Utils/Maps.v`).
-/

@[expose] public section
namespace Tisl.Ctx

/-- A context maps variable names to naturals. -/
abbrev Ctx := List (String × Nat)

/-- Look up the value bound to `k`. -/
def lookup (k : String) (m : Ctx) : Option Nat := m.lookup k

/-- Bind `k` to `v`, removing any previous binding of `k`. -/
def add (k : String) (v : Nat) (m : Ctx) : Ctx := (k, v) :: m.filter (fun p => p.1 != k)

/-- `c` is bound to a value satisfying `p`. -/
def assert1 (c : String) (m : Ctx) (p : Nat → Prop) : Prop :=
  ∃ v, lookup c m = some v ∧ p v

/-- `c1` and `c2` are bound to values related by `r`. -/
def assert2 (c1 c2 : String) (m : Ctx) (r : Nat → Nat → Prop) : Prop :=
  ∃ v1 v2, lookup c1 m = some v1 ∧ lookup c2 m = some v2 ∧ r v1 v2

@[simp] theorem lookup_add_eq (c : String) (v : Nat) (m : Ctx) : lookup c (add c v m) = some v := by
  simp [lookup, add]

@[simp] theorem lookup_add_neq (c r : String) (v : Nat) (m : Ctx) (h : r ≠ c) :
    lookup c (add r v m) = lookup c m := by
  have hc : (c == r) = false := by simpa using Ne.symm h
  simp only [lookup, add, List.lookup_cons, hc]
  induction m with
  | nil => rfl
  | cons p m ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k = r
    · subst hk; simp [List.filter, List.lookup_cons, hc, ih]
    · have : (k != r) = true := by simpa using hk
      simp only [List.filter, this, List.lookup_cons]
      split <;> simp_all

theorem assert1_add_eq (c : String) (v : Nat) (m : Ctx) (p : Nat → Prop) (h : p v) :
    assert1 c (add c v m) p := ⟨v, lookup_add_eq c v m, h⟩

theorem assert1_add_neq (c1 c2 : String) (v : Nat) (m : Ctx) (p : Nat → Prop)
    (h : assert1 c1 m p) (hne : c1 ≠ c2) : assert1 c1 (add c2 v m) p := by
  obtain ⟨v1, hc, hv⟩ := h
  exact ⟨v1, by rw [lookup_add_neq _ _ _ _ (Ne.symm hne), hc], hv⟩

theorem assert2_add_l (c1 c2 : String) (v1 v2 : Nat) (m : Ctx) (p : Nat → Nat → Prop)
    (hne : c1 ≠ c2) (h : p v1 v2) : assert2 c1 c2 (add c1 v1 (add c2 v2 m)) p :=
  ⟨v1, v2, lookup_add_eq _ _ _, by rw [lookup_add_neq _ _ _ _ hne, lookup_add_eq], h⟩

end Tisl.Ctx
