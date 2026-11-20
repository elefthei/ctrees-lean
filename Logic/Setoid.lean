/- SPDX-License-Identifier: MIT -/
module

public import Logic.Semantics

/-!
# Kripke setoids

An equivalence `meq` on models is a Kripke setoid when every step of `s` from `w` is matched by a
step of any `meq`-equivalent `t` to an `meq`-equivalent model. Such an equivalence preserves every
TICL formula, including suffix formulas with postconditions (← `Logic/Setoid.v`).
-/

@[expose] public section
namespace Tisl
open ITree (Effect)
open Coinduction

/-- `meq` is an equivalence on `M E B X` and the square
`meq s t`, `ktrans s w s' w'` ⟹ `∃ t', ktrans t w t' w' ∧ meq s' t'` commutes. -/
class KripkeSetoid (M : Effect.{u} → Effect.{u} → Type u → Type u) (E B : Effect.{u})
    [Kripke M E B] (X : Type u) (meq : M E B X → M E B X → Prop) : Prop where
  equiv : Equivalence meq
  ktrans_semiproper {t s s' : M E B X} {w w' : World E} :
    meq s t → ktrans s w s' w' → ∃ t', ktrans t w t' w' ∧ meq s' t'

export KripkeSetoid (ktrans_semiproper)

variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {E B : Effect.{u}} [Kripke M E B]
  {X : Type u} {meq : M E B X → M E B X → Prop} [KS : KripkeSetoid M E B X meq]
set_option hygiene false in
local notation "MP" => M E B X → World E → Prop

/-- `ktrans_semiproper` with the equivalence used right-to-left. -/
private theorem ktrans_semiproper_symm {t u t' : M E B X} {w w' : World E} (h : meq t u)
    (tr : ktrans u w t' w') : ∃ u', ktrans t w u' w' ∧ meq t' u' :=
  ktrans_semiproper (KS.equiv.symm h) tr

theorem proper_can_step {t u : M E B X} {w : World E} (h : meq t u) :
    can_step t w ↔ can_step u w :=
  ⟨fun ⟨_, w', tr⟩ => let ⟨u', tr', _⟩ := ktrans_semiproper h tr; ⟨u', w', tr'⟩,
   fun ⟨_, w', tr⟩ => let ⟨t', tr', _⟩ := ktrans_semiproper_symm h tr; ⟨t', w', tr'⟩⟩

omit [Kripke M E B] KS in
/-- Constant predicates are congruences. -/
theorem meq_proper_fun {φ : World E → Prop} {t u : M E B X} {w : World E} (_ : meq t u) :
    (fun (_ : M E B X) => φ) t w ↔ (fun (_ : M E B X) => φ) u w := Iff.rfl

/-! ## Congruence of the binary modalities -/

section Binary
variable {P Q : MP} (hP : ∀ t u w, meq t u → (P t w ↔ P u w))
  (hQ : ∀ t u w, meq t u → (Q t w ↔ Q u w))
include hP hQ

private theorem anc_meq {t u : M E B X} {w : World E} (h : meq t u) (H : anc P Q t w) :
    anc P Q u w :=
  have ⟨hp, hs, hk⟩ := H
  ⟨(hP _ _ _ h).1 hp, (proper_can_step h).1 hs, fun _ _ tr =>
    let ⟨_, tr', h'⟩ := ktrans_semiproper_symm h tr; (hQ _ _ _ h').2 (hk _ _ tr')⟩

/-- `anc` is a congruence with regards to `meq`. -/
theorem proper_ax_equ {t u : M E B X} {w : World E} (h : meq t u) :
    anc P Q t w ↔ anc P Q u w :=
  ⟨anc_meq hP hQ h, anc_meq hP hQ (KS.equiv.symm h)⟩

private theorem enc_meq {t u : M E B X} {w : World E} (h : meq t u) (H : enc P Q t w) :
    enc P Q u w :=
  have ⟨hp, _, w', tr, hq⟩ := H
  let ⟨u', tr', h'⟩ := ktrans_semiproper h tr
  ⟨(hP _ _ _ h).1 hp, u', w', tr', (hQ _ _ _ h').1 hq⟩

/-- `enc` is a congruence with regards to `meq`. -/
theorem proper_ex_equ {t u : M E B X} {w : World E} (h : meq t u) :
    enc P Q t w ↔ enc P Q u w :=
  ⟨enc_meq hP hQ h, enc_meq hP hQ (KS.equiv.symm h)⟩

private theorem auc_meq {t u : M E B X} {w : World E} (h : meq t u) (H : Auc P Q t w) :
    Auc P Q u w := by
  induction H generalizing u with
  | matchA hq => exact .matchA ((hQ _ _ _ h).1 hq)
  | stepA hp hs _ ih =>
    exact .stepA ((hP _ _ _ h).1 hp) ((proper_can_step h).1 hs) fun _ _ tr =>
      let ⟨_, tr', h'⟩ := ktrans_semiproper_symm h tr; ih _ _ tr' (KS.equiv.symm h')

/-- `Auc` is a congruence with regards to `meq`. -/
theorem proper_au_equ {t u : M E B X} {w : World E} (h : meq t u) :
    Auc P Q t w ↔ Auc P Q u w :=
  ⟨auc_meq hP hQ h, auc_meq hP hQ (KS.equiv.symm h)⟩

private theorem euc_meq {t u : M E B X} {w : World E} (h : meq t u) (H : Euc P Q t w) :
    Euc P Q u w := by
  induction H generalizing u with
  | matchE hq => exact .matchE ((hQ _ _ _ h).1 hq)
  | stepE _ w' hp tr _ ih =>
    obtain ⟨u', tr', h'⟩ := ktrans_semiproper h tr
    exact .stepE u' w' ((hP _ _ _ h).1 hp) tr' (ih h')

/-- `Euc` is a congruence with regards to `meq`. -/
theorem proper_eu_equ {t u : M E B X} {w : World E} (h : meq t u) :
    Euc P Q t w ↔ Euc P Q u w :=
  ⟨euc_meq hP hQ h, euc_meq hP hQ (KS.equiv.symm h)⟩

theorem proper_qnext_equ (q : Ticlq) {t u : M E B X} {w : World E} (h : meq t u) :
    qnext q P Q t w ↔ qnext q P Q u w := by
  cases q
  · exact proper_ax_equ hP hQ h
  · exact proper_ex_equ hP hQ h

theorem proper_quntil_equ (q : Ticlq) {t u : M E B X} {w : World E} (h : meq t u) :
    quntil q P Q t w ↔ quntil q P Q u w := by
  cases q
  · exact proper_au_equ hP hQ h
  · exact proper_eu_equ hP hQ h

end Binary

/-! ## Congruence of the greatest fixpoints `agc`, `egc`

Properness is inf-closed, so it propagates along the whole final chain of `agcF P`/`egcF P` (tower
induction), hence to every chain element used in a proof by coinduction, and to the `gfp`. -/

section Global
variable {P : MP} (hP : ∀ t u w, meq t u → (P t w ↔ P u w))

omit [Kripke M E B] [KripkeSetoid M E B X meq] in
theorem inf_closed_proper_meq :
    InfClosed fun R : Rel (M E B X) (World E) => ∀ t u w, meq t u → (R t w ↔ R u w) :=
  fun _ hT t u w h => by
    simp only [Rel.inf_apply]
    exact ⟨fun H R hR => (hT R hR t u w h).1 (H R hR), fun H R hR => (hT R hR t u w h).2 (H R hR)⟩

include hP

/-- Every element of the final chain of `agcF P` is a congruence. -/
theorem agc_chain_proper :
    ∀ R, Chain (agcF P) R → ∀ t u w, meq t u → (R t w ↔ R u w) :=
  tower inf_closed_proper_meq fun _ _ hR _ _ _ h => proper_ax_equ hP hR h

/-- Every element of the final chain of `egcF P` is a congruence. -/
theorem egc_chain_proper :
    ∀ R, Chain (egcF P) R → ∀ t u w, meq t u → (R t w ↔ R u w) :=
  tower inf_closed_proper_meq fun _ _ hR _ _ _ h => proper_ex_equ hP hR h

theorem proper_agc_chain_equ {R} (hR : Chain (agcF P) R) {t u : M E B X} {w : World E}
    (h : meq t u) : R t w ↔ R u w :=
  agc_chain_proper hP R hR t u w h

theorem proper_egc_chain_equ {R} (hR : Chain (egcF P) R) {t u : M E B X} {w : World E}
    (h : meq t u) : R t w ↔ R u w :=
  egc_chain_proper hP R hR t u w h

/-- `agc` is a congruence with regards to `meq`. -/
theorem proper_ag_equ {t u : M E B X} {w : World E} (h : meq t u) : agc P t w ↔ agc P u w :=
  proper_agc_chain_equ hP (gfp_chain _) h

/-- `egc` is a congruence with regards to `meq`. -/
theorem proper_er_equ {t u : M E B X} {w : World E} (h : meq t u) : egc P t w ↔ egc P u w :=
  proper_egc_chain_equ hP (gfp_chain _) h

end Global

/-! ## Congruence with respect to TICL formulas -/

/-- `entails` preserves model equivalence at every formula index. -/
theorem proper_entails_meq {i : Option (Type u)} (φ : Ticl E i) {t u : M E B X} {w : World E}
    (h : meq t u) : entails φ t w ↔ entails φ u w := by
  induction φ generalizing t u w with
  | now p => exact Iff.rfl
  | ret p =>
    exact exists_congr fun _ => and_congr_right fun _ =>
      proper_ax_equ (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl) h
  | cu q p r ihp ihr =>
    rw [entails_cu, entails_cu]
    exact proper_quntil_equ (P := entails p) (Q := entails r) (fun _ _ _ h => ihp h)
      (fun _ _ _ h => ihr h) q h
  | cx q p r ihp ihr =>
    rw [entails_cx, entails_cx]
    exact proper_qnext_equ (P := entails p) (Q := entails r) (fun _ _ _ h => ihp h)
      (fun _ _ _ h => ihr h) q h
  | cg q p ihp =>
    cases q
    · exact proper_ag_equ (P := entails p) (fun _ _ _ h => ihp h) h
    · exact proper_er_equ (P := entails p) (fun _ _ _ h => ihp h) h
  | and p r ihp ihr => exact and_congr (ihp h) (ihr h)
  | or p r ihp ihr => exact or_congr (ihp h) (ihr h)

-- Not ported: the Ltac `ktrans_equ` (replaced by `ktrans_semiproper` and the private
-- `ktrans_semiproper_symm`).

end Tisl
