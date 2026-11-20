/- SPDX-License-Identifier: MIT -/
module

public import CTree.Core.Utils

/-!
# Relations, ranks and counting

Lexicographic ranks over `Nat`, occurrence/counting predicates on index sequences, first-index
search in finite intervals and bounded-credit progress (← `Utils/Relations.v`).
-/

@[expose] public section
namespace Tisl
open CTree (Star)

theorem nat_iter_add_const (n k x : Nat) : Nat.repeat (Nat.add k) n x = n * k + x := by
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih => simp only [Nat.repeat, ih, Nat.succ_mul, Nat.add_eq]; omega

theorem clos_refl_trans_preserves {A} (R : A → A → Prop) (I : A → Prop) :
    (∀ x y, I x → R x y → I y) → ∀ x y, I x → Star R x y → I y := by
  intro hstep x y hx hpath
  induction hpath with
  | refl => exact hx
  | tail _ hbc ih => exact hstep _ _ ih hbc

theorem acc_self_loop {A} (R : A → A → Prop) (x : A) : R x x → ¬ Acc R x := by
  intro hloop hacc
  induction hacc with
  | intro x _ ih => exact ih x hloop hloop

/-- One natural-number lexicographic layer over an arbitrary relation. -/
def lexn {A} (R : A → A → Prop) : Nat × A → Nat × A → Prop := Prod.Lex (· < ·) R

theorem lexn_wf {A} (R : A → A → Prop) : WellFounded R → WellFounded (lexn R) :=
  fun hR => (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨R, hR⟩).wf

/-- Lexicographic order on pairs of naturals. -/
def lexnat : Nat × Nat → Nat × Nat → Prop := lexn (· < ·)

theorem lexnat_wf : WellFounded lexnat := lexn_wf _ Nat.lt_wfRel.wf

/-- Lexicographic order on triples of naturals. -/
def rank3 : Nat × (Nat × Nat) → Nat × (Nat × Nat) → Prop := lexn (lexn (· < ·))

theorem rank3_wf : WellFounded rank3 := lexn_wf _ (lexn_wf _ Nat.lt_wfRel.wf)

/-- Decrease in the first component of a triple. -/
theorem rank3_bound (b b' p p' q q' : Nat) : b' < b → rank3 (b', (p', q')) (b, (p, q)) :=
  fun h => .left _ _ h

/-- Decrease in the second component of a triple. -/
theorem rank3_pos (b p p' q q' : Nat) : p' < p → rank3 (b, (p', q')) (b, (p, q)) :=
  fun h => .right _ (.left _ _ h)

/-- Decrease in the third component of a triple. -/
theorem rank3_phase (b p q q' : Nat) : q' < q → rank3 (b, (p, q')) (b, (p, q)) :=
  fun h => .right _ (.right _ h)

/-- Occurrences arbitrarily far along a sequence. -/
def infinitely (P : Nat → Prop) : Prop := ∀ n, ∃ k, n ≤ k ∧ P k

/-- Number of indices in `[lo, lo + len)` satisfying `p`. -/
def count_if (p : Nat → Bool) (lo len : Nat) : Nat := ((List.range' lo len).filter p).length

@[simp] theorem count_if_zero (p : Nat → Bool) (lo : Nat) : count_if p lo 0 = 0 := rfl

theorem count_if_succ (p : Nat → Bool) (lo len : Nat) :
    count_if p lo (len + 1) = (if p lo then 1 else 0) + count_if p (lo + 1) len := by
  simp only [count_if, List.range'_succ, List.filter_cons]
  split <;> simp [Nat.add_comm]

theorem count_if_add (p : Nat → Bool) (lo left right : Nat) :
    count_if p lo (left + right) = count_if p lo left + count_if p (lo + left) right := by
  simp only [count_if, ← List.range'_append_1, List.filter_append, List.length_append]

theorem infinitely_count_if (p : Nat → Bool) :
    infinitely (fun k => p k = true) → ∀ wanted lo, ∃ len, wanted ≤ count_if p lo len := by
  intro hinf wanted
  induction wanted with
  | zero => intro lo; exact ⟨0, Nat.zero_le _⟩
  | succ wanted ih =>
    intro lo
    obtain ⟨k, hlo, hk⟩ := hinf lo
    obtain ⟨len, hlen⟩ := ih (k + 1)
    refine ⟨(k - lo) + (len + 1), ?_⟩
    rw [count_if_add, show lo + (k - lo) = k by omega, count_if_succ, hk]
    simp only [ite_true]
    omega

/-- Find the first satisfying index in a finite interval, or establish that the whole interval has
no satisfying index. -/
theorem finite_first (P : Nat → Prop) (dec : ∀ j, Decidable (P j)) (lo len : Nat) :
    (∀ j, lo ≤ j ∧ j < lo + len → ¬ P j) ∨
      ∃ j, (lo ≤ j ∧ j < lo + len) ∧ P j ∧ ∀ i, lo ≤ i ∧ i < j → ¬ P i := by
  induction len generalizing lo with
  | zero => exact .inl fun j hj => absurd hj.2 (by omega)
  | succ len ih =>
    by_cases hyes : P lo
    · exact .inr ⟨lo, ⟨Nat.le_refl _, by omega⟩, hyes, fun i hi => absurd hi.2 (by omega)⟩
    · rcases ih (lo + 1) with hnone | ⟨j, hj, hP, hfirst⟩
      · refine .inl fun i hi => ?_
        if h : i = lo then exact h ▸ hyes else exact hnone i ⟨by omega, by omega⟩
      · refine .inr ⟨j, ⟨by omega, by omega⟩, hP, fun i hi => ?_⟩
        if h : i = lo then exact h ▸ hyes else exact hfirst i ⟨by omega, hi.2⟩

/-- Boolean existence search is a projection of the same first-index search. -/
theorem finite_bool_search (p : Nat → Bool) (lo len : Nat) :
    (∃ k, (lo ≤ k ∧ k < lo + len) ∧ p k = true) ∨
      (∀ k, lo ≤ k ∧ k < lo + len → p k = false) := by
  rcases finite_first (fun k => p k = true) inferInstance lo len with hnone | ⟨k, hk, hp, -⟩
  · exact .inr fun k hk => by simpa using hnone k hk
  · exact .inl ⟨k, hk, hp⟩

/-! ## Bounded-credit progress

A `Credit` relation that descends by at least the charge of every goal-free step bounds how many
charged indices can pass before the goal is met. Charging counts selected useful indices, not
elapsed time; the zero-length interval cannot fabricate a hit. -/

theorem credit_interval (Credit : Nat → Nat → Prop) (charged : Nat → Bool) (goal : Nat → Prop)
    (step : ∀ k credit, Credit k credit → ¬ goal k →
      ∃ credit', Credit (k + 1) credit' ∧ (if charged k then 1 else 0) + credit' ≤ credit) :
    ∀ lo len credit, Credit lo credit → (∀ k, lo ≤ k ∧ k < lo + len → ¬ goal k) →
      ∃ credit', Credit (lo + len) credit' ∧ count_if charged lo len + credit' ≤ credit := by
  intro lo len
  induction len generalizing lo with
  | zero => intro credit hc _; exact ⟨credit, hc, by simp⟩
  | succ len ih =>
    intro credit hc hno
    obtain ⟨mid, hmid, hdrop⟩ := step lo credit hc (hno lo ⟨Nat.le_refl _, by omega⟩)
    obtain ⟨credit', hcredit', hcount⟩ :=
      ih (lo + 1) mid hmid fun k hk => hno k ⟨by omega, by omega⟩
    refine ⟨credit', by rwa [show lo + (len + 1) = lo + 1 + len by omega], ?_⟩
    rw [count_if_succ]
    split at hdrop <;> simp_all <;> omega

/-- The first goal index inside an interval whose charge reaches a bound that no goal-free prefix
can reach. -/
theorem count_if_first (charged : Nat → Bool) (goal : Nat → Prop) (dec : ∀ k, Decidable (goal k))
    (lo len bound : Nat) :
    (∀ n, (∀ k, lo ≤ k ∧ k < lo + n → ¬ goal k) → count_if charged lo n < bound) →
    bound ≤ count_if charged lo len →
    ∃ k, (lo ≤ k ∧ k < lo + len) ∧ goal k ∧ count_if charged lo (k + 1 - lo) ≤ bound := by
  intro hprefix hreach
  rcases finite_first goal dec lo len with hnone | ⟨k, hk, hgoal, hfirst⟩
  · exact absurd (hprefix len hnone) (by omega)
  · refine ⟨k, hk, hgoal, ?_⟩
    -- The charge through `k` is the goal-free prefix (strictly below `bound`) plus at most one.
    have hpre : count_if charged lo (k - lo) < bound :=
      hprefix _ fun i hi => hfirst i ⟨hi.1, by omega⟩
    rw [show k + 1 - lo = (k - lo) + 1 by omega, count_if_add,
      show lo + (k - lo) = k by omega, count_if_succ, count_if_zero]
    split <;> omega

/-- If every goal-free interval has bounded charge and charging happens infinitely often, the goal
is met infinitely often. -/
theorem infinitely_progress (charged : Nat → Bool) (goal : Nat → Prop)
    (dec : ∀ k, Decidable (goal k)) :
    (∀ lo, ∃ bound, ∀ len, (∀ k, lo ≤ k ∧ k < lo + len → ¬ goal k) →
      count_if charged lo len < bound) →
    infinitely (fun k => charged k = true) → infinitely goal := by
  intro hbound hinf n
  obtain ⟨bound, hprefix⟩ := hbound n
  obtain ⟨len, hlen⟩ := infinitely_count_if charged hinf bound n
  obtain ⟨k, hk, hgoal, -⟩ := count_if_first charged goal dec n len bound hprefix hlen
  exact ⟨k, hk.1, hgoal⟩

end Tisl
