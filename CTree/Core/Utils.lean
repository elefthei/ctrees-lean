/- SPDX-License-Identifier: MIT -/
module

public import ITree.Effect

/-!
# Utilities

Monad classes for the effects a `CTree` can be interpreted into, the reflexive-transitive closure
of a relation, and the sum of two relations (← `Core/Utils.v`).
-/

@[expose] public section
namespace CTree
open ITree (Effect)

/-- Monads that can trigger the events of `E`. -/
class MonadTrigger (E : Effect.{u}) (M : Type u → Type u) where
  mtrigger : (e : E.I) → M (E.O e)

/-- Monads that can branch over the indices of `B`. -/
class MonadBr (B : Effect.{u}) (M : Type u → Type u) where
  mbr : (c : B.I) → M (B.O c)

/-- Monads with an observable internal step. -/
class MonadStep (M : Type u → Type u) where
  mstep : M PUnit

/-- Monads with a stuck (deadlocked) computation. -/
class MonadStuck (M : Type u → Type u) where
  mstuck : {X : Type u} → M X

export MonadTrigger (mtrigger)
export MonadBr (mbr)
export MonadStep (mstep)
export MonadStuck (mstuck)

/-- Reflexive-transitive closure (Rocq/RelationAlgebra `r^*`; `Relation.TransGen r` is `r^+`). -/
inductive Star {α : Sort v} (r : α → α → Prop) (a : α) : α → Prop
  | refl : Star r a a
  | tail {b c} : Star r a b → r b c → Star r a c

namespace Star
variable {α : Sort v} {r : α → α → Prop} {a b c : α}

theorem single (h : r a b) : Star r a b := tail refl h

theorem trans (h₁ : Star r a b) (h₂ : Star r b c) : Star r a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact tail ih h

theorem head (h₁ : r a b) (h₂ : Star r b c) : Star r a c := trans (single h₁) h₂

theorem cases_head (h : Star r a c) : a = c ∨ ∃ b, r a b ∧ Star r b c := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | ⟨b', hab', hb'⟩
    · exact .inr ⟨_, hbc, refl⟩
    · exact .inr ⟨b', hab', tail hb' hbc⟩

/-- Induction from the head: the predicate is propagated backwards along `r`. -/
theorem head_induction_on {P : α → Prop} (h : Star r a c) (refl : P c)
    (head : ∀ {a b}, r a b → Star r b c → P b → P a) : P a := by
  induction h with
  | refl => exact refl
  | @tail b c' hab hbc ih =>
    exact ih (head hbc .refl refl) fun h1 h2 h3 => head h1 (Star.tail h2 hbc) h3

theorem iff_transGen : Star r a b ↔ a = b ∨ Relation.TransGen r a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .inl rfl
    | tail _ hbc ih =>
      rcases ih with rfl | h
      · exact .inr (.single hbc)
      · exact .inr (.tail h hbc)
  · rintro (rfl | h)
    · exact refl
    · induction h with
      | single h => exact single h
      | tail _ h ih => exact tail ih h

theorem of_transGen (h : Relation.TransGen r a b) : Star r a b := iff_transGen.2 (.inr h)

theorem mono {r s : α → α → Prop} (hrs : ∀ x y, r x y → s x y) (h : Star r a b) : Star s a b := by
  induction h with
  | refl => exact refl
  | tail _ h ih => exact tail ih (hrs _ _ h)

end Star

/-- `r^* ⋅ r^+ ⊆ r^+`. -/
theorem Star.trans_transGen {α : Sort v} {r : α → α → Prop} {a b c : α}
    (h₁ : Star r a b) (h₂ : Relation.TransGen r b c) : Relation.TransGen r a c := by
  rcases iff_transGen.1 h₁ with rfl | h₁
  · exact h₂
  · exact h₁.trans h₂

/-- `r^+ ⋅ r^* ⊆ r^+`. -/
theorem Star.transGen_trans {α : Sort v} {r : α → α → Prop} {a b c : α}
    (h₁ : Relation.TransGen r a b) (h₂ : Star r b c) : Relation.TransGen r a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail ih h

/-- The sum of two relations. -/
def sumRel {A1 A2 B1 B2 : Type u} (Ra : A1 → A2 → Prop) (Rb : B1 → B2 → Prop) :
    A1 ⊕ B1 → A2 ⊕ B2 → Prop
  | .inl a, .inl a' => Ra a a'
  | .inr b, .inr b' => Rb b b'
  | _, _ => False

end CTree
