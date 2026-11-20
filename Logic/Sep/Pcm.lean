/- SPDX-License-Identifier: MIT -/
module

/-!
# Partial commutative monoids

Setoid PCMs presented by a total composition `pop` with a definedness predicate `pdef` and a carrier
equivalence `peq`; generic spatial assertions (`⋆`, `-⋆`) over them; componentwise products and a
non-cancellative witness `BoolPCM` (← `Utils/Pcm.v`).
-/

@[expose] public section
namespace Tisl.Pcm

universe u v

/-- A partial commutative monoid with explicit definedness and a justified equivalence.
Cancellativity is deliberately *not* a field (see `Cancellative`). -/
class PCM (A : Type u) where
  /-- the justified equivalence on the carrier -/
  peq : A → A → Prop
  /-- definedness / compatibility of a composition -/
  pdef : A → A → Prop
  /-- the composition, meaningful exactly when `pdef` holds -/
  pop : A → A → A
  /-- the unit -/
  pemp : A
  peq_refl : ∀ a, peq a a
  peq_sym : ∀ a b, peq a b → peq b a
  peq_trans : ∀ a b c, peq a b → peq b c → peq a c
  /-- both `pdef` and `pop` respect the equivalence -/
  pdef_resp : ∀ a a' b b', peq a a' → peq b b' → pdef a b → pdef a' b'
  pop_resp : ∀ a a' b b', peq a a' → peq b b' → peq (pop a b) (pop a' b')
  /-- commutativity, in both components -/
  pdef_comm : ∀ a b, pdef a b → pdef b a
  pop_comm : ∀ a b, pdef a b → peq (pop a b) (pop b a)
  /-- unit laws -/
  pdef_emp : ∀ a, pdef pemp a
  pop_emp : ∀ a, peq (pop pemp a) a
  /-- associativity, with the definedness bookkeeping made explicit -/
  pdef_assocL : ∀ a b c, pdef b c → pdef a (pop b c) → pdef a b
  pdef_assocR : ∀ a b c, pdef b c → pdef a (pop b c) → pdef (pop a b) c
  pdef_assocI : ∀ a b c, pdef b c → pdef a b → pdef (pop a b) c → pdef a (pop b c)
  pop_assoc : ∀ a b c, pdef b c → pdef a (pop b c) → peq (pop a (pop b c)) (pop (pop a b) c)

export PCM (peq pdef pop pemp peq_refl peq_sym peq_trans pdef_resp pop_resp pdef_comm pop_comm
  pdef_emp pop_emp pdef_assocL pdef_assocR pdef_assocI pop_assoc)

@[inherit_doc] scoped infixl:65 " ⊎ " => pop
@[inherit_doc] scoped infix:50 " # " => pdef
@[inherit_doc] scoped infix:50 (priority := high) " ≈ " => peq

/-- Cancellativity is a *separate* property: everything proved assuming only `PCM` is, by
construction, independent of it. -/
def Cancellative (A : Type u) [PCM A] : Prop :=
  ∀ a b c : A, a # b → a # c → a ⊎ b ≈ a ⊎ c → b ≈ c

section PcmFacts
variable {A : Type u} [PCM A]

theorem pop_emp_r (a : A) : a # pemp → a ⊎ pemp ≈ a :=
  fun hd => peq_trans _ _ _ (pop_comm _ _ hd) (pop_emp a)

theorem pdef_emp_r (a : A) : a # pemp := pdef_comm _ _ (pdef_emp a)

/-- The "other" associativity direction, derived. -/
theorem pop_assoc' (a b c : A) : b # c → a # (b ⊎ c) → (a ⊎ b) ⊎ c ≈ a ⊎ (b ⊎ c) :=
  fun h1 h2 => peq_sym _ _ (pop_assoc _ _ _ h1 h2)

end PcmFacts

/-! ## Spatial assertions over an arbitrary PCM -/

/-- Assertions on a resource. -/
def assn (A : Type u) := A → Prop

section Assertions
variable {A : Type u} [PCM A]

/-- An assertion is well formed when it does not distinguish equivalent resources. -/
def AProper (P : assn A) : Prop := ∀ a b, a ≈ b → P a → P b

def aemp : assn A := fun a => a ≈ pemp

def asep (P Q : assn A) : assn A :=
  fun a => ∃ a₁ a₂, a₁ # a₂ ∧ a ≈ a₁ ⊎ a₂ ∧ P a₁ ∧ Q a₂

def awand (P Q : assn A) : assn A :=
  fun a => ∀ b, a # b → P b → Q (a ⊎ b)

def atrue : assn A := fun _ => True

theorem aemp_proper : AProper (aemp (A := A)) :=
  fun _ _ hab ha => peq_trans _ _ _ (peq_sym _ _ hab) ha

theorem asep_proper (P Q : assn A) : AProper (asep P Q) := by
  rintro a b hab ⟨a₁, a₂, hd, he, hP, hQ⟩
  exact ⟨a₁, a₂, hd, peq_trans _ _ _ (peq_sym _ _ hab) he, hP, hQ⟩

theorem asep_pinned (a b : A) (P Q : Prop) (hd : a # b) :
    asep (fun x => x ≈ a ∧ P) (fun y => y ≈ b ∧ Q) (a ⊎ b) ↔ P ∧ Q := by
  constructor
  · rintro ⟨_, _, _, _, ⟨_, hP⟩, ⟨_, hQ⟩⟩; exact ⟨hP, hQ⟩
  · rintro ⟨hP, hQ⟩; exact ⟨a, b, hd, peq_refl _, ⟨peq_refl _, hP⟩, ⟨peq_refl _, hQ⟩⟩

/-- `⋆` is commutative. -/
theorem asep_comm (P Q : assn A) (a : A) : asep P Q a → asep Q P a := by
  rintro ⟨a₁, a₂, hd, he, hP, hQ⟩
  exact ⟨a₂, a₁, pdef_comm _ _ hd, peq_trans _ _ _ he (pop_comm _ _ hd), hQ, hP⟩

/-- `emp` is a left unit, in both directions. -/
theorem asep_emp_l (P : assn A) (a : A) (_ : AProper P) (ha : P a) : asep aemp P a :=
  ⟨pemp, a, pdef_emp _, peq_sym _ _ (pop_emp _), peq_refl _, ha⟩

theorem asep_emp_l_inv (P : assn A) (a : A) (hP : AProper P) : asep aemp P a → P a := by
  rintro ⟨a₁, a₂, _, he, hemp, hQ⟩
  refine hP _ _ (peq_sym _ _ ?_) hQ
  exact peq_trans _ _ _ he
    (peq_trans _ _ _ (pop_resp _ _ _ _ hemp (peq_refl _)) (pop_emp _))

/-- `⋆` is associative, one direction shown (the other is symmetric). -/
theorem asep_assoc (P Q R : assn A) (a : A) : asep P (asep Q R) a → asep (asep P Q) R a := by
  rintro ⟨a₁, a₂₃, hd₁, he₁, hP, a₂, a₃, hd₂, he₂, hQ, hR⟩
  have hd₁' : a₁ # (a₂ ⊎ a₃) := pdef_resp _ _ _ _ (peq_refl _) he₂ hd₁
  refine ⟨a₁ ⊎ a₂, a₃, pdef_assocR _ _ _ hd₂ hd₁', ?_,
    ⟨a₁, a₂, pdef_assocL _ _ _ hd₂ hd₁', peq_refl _, hP, hQ⟩, hR⟩
  exact peq_trans _ _ _ he₁
    (peq_trans _ _ _ (pop_resp _ _ _ _ (peq_refl _) he₂) (pop_assoc _ _ _ hd₂ hd₁'))

/-- Monotonicity: the frame rule of the spatial layer. -/
theorem asep_mono (P P' Q Q' : assn A) (a : A) (hP : ∀ x, P x → P' x) (hQ : ∀ x, Q x → Q' x) :
    asep P Q a → asep P' Q' a := by
  rintro ⟨a₁, a₂, hd, he, h₁, h₂⟩
  exact ⟨a₁, a₂, hd, he, hP _ h₁, hQ _ h₂⟩

/-- The wand adjunction, introduction direction. -/
theorem awand_intro (P Q R : assn A) (hpq : ∀ a, asep P Q a → R a) (a : A) (ha : P a) :
    awand Q R a :=
  fun b hd hQ => hpq _ ⟨a, b, hd, peq_refl _, ha, hQ⟩

/-- The wand adjunction, elimination direction. -/
theorem awand_elim (P Q : assn A) (a : A) : asep (awand P Q) P a → AProper Q → Q a := by
  rintro ⟨a₁, a₂, hd, he, hw, hP⟩ hQ
  exact hQ _ _ (peq_sym _ _ he) (hw _ hd hP)

end Assertions

@[inherit_doc] scoped infixr:60 " ⋆ " => asep
@[inherit_doc] scoped infixr:55 " -⋆ " => awand

/-! ## Componentwise products and a non-cancellative PCM -/

/-- Equivalence, definedness and composition are componentwise; the unit is the pair of units. -/
instance ProductPCM {A : Type u} {B : Type v} [PA : PCM A] [PB : PCM B] : PCM (A × B) where
  peq x y := x.1 ≈ y.1 ∧ x.2 ≈ y.2
  pdef x y := x.1 # y.1 ∧ x.2 # y.2
  pop x y := (x.1 ⊎ y.1, x.2 ⊎ y.2)
  pemp := (pemp, pemp)
  peq_refl _ := ⟨peq_refl _, peq_refl _⟩
  peq_sym _ _ h := ⟨peq_sym _ _ h.1, peq_sym _ _ h.2⟩
  peq_trans _ _ _ h h' := ⟨peq_trans _ _ _ h.1 h'.1, peq_trans _ _ _ h.2 h'.2⟩
  pdef_resp _ _ _ _ ha hb hd := ⟨pdef_resp _ _ _ _ ha.1 hb.1 hd.1, pdef_resp _ _ _ _ ha.2 hb.2 hd.2⟩
  pop_resp _ _ _ _ ha hb := ⟨pop_resp _ _ _ _ ha.1 hb.1, pop_resp _ _ _ _ ha.2 hb.2⟩
  pdef_comm _ _ h := ⟨pdef_comm _ _ h.1, pdef_comm _ _ h.2⟩
  pop_comm _ _ h := ⟨pop_comm _ _ h.1, pop_comm _ _ h.2⟩
  pdef_emp _ := ⟨pdef_emp _, pdef_emp _⟩
  pop_emp _ := ⟨pop_emp _, pop_emp _⟩
  pdef_assocL _ _ _ h h' := ⟨pdef_assocL _ _ _ h.1 h'.1, pdef_assocL _ _ _ h.2 h'.2⟩
  pdef_assocR _ _ _ h h' := ⟨pdef_assocR _ _ _ h.1 h'.1, pdef_assocR _ _ _ h.2 h'.2⟩
  pdef_assocI _ _ _ h h' h'' :=
    ⟨pdef_assocI _ _ _ h.1 h'.1 h''.1, pdef_assocI _ _ _ h.2 h'.2 h''.2⟩
  pop_assoc _ _ _ h h' := ⟨pop_assoc _ _ _ h.1 h'.1, pop_assoc _ _ _ h.2 h'.2⟩

/-- Carrier `Bool`, composition `||`, always defined, unit `false`: every PCM law holds but
cancellativity does not. -/
instance BoolPCM : PCM Bool where
  peq := Eq
  pdef _ _ := True
  pop := (· || ·)
  pemp := false
  peq_refl _ := rfl
  peq_sym _ _ := Eq.symm
  peq_trans _ _ _ := Eq.trans
  pdef_resp _ _ _ _ _ _ _ := trivial
  pop_resp _ _ _ _ ha hb := ha ▸ hb ▸ rfl
  pdef_comm _ _ _ := trivial
  pop_comm a b _ := Bool.or_comm a b
  pdef_emp _ := trivial
  pop_emp _ := rfl
  pdef_assocL _ _ _ _ _ := trivial
  pdef_assocR _ _ _ _ _ := trivial
  pdef_assocI _ _ _ _ _ _ := trivial
  pop_assoc a b c _ _ := (Bool.or_assoc a b c).symm

theorem bool_pcm_not_cancellative : ¬ Cancellative Bool := fun hc =>
  absurd (hc true true false trivial trivial rfl) Bool.noConfusion

end Tisl.Pcm
