/- SPDX-License-Identifier: MIT -/
module

public import Logic.Syntax
public import CTree.Coinduction

/-!
# TICL semantics

Shallow embedding of TICL over a Kripke model: the next modalities `anc`/`enc`, the inductive
until modalities `Auc`/`Euc`, the coinductive always modalities `agc`/`egc`, and the entailment
`entails φ t w`, defined by structural recursion on the indexed formula (← `Logic/Semantics.v`).
-/

@[expose] public section
namespace Tisl
open ITree (Effect)
open CTree.Coinduction

variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {E B : Effect.{u}} [Kripke M E B]
  {X : Type u}
set_option hygiene false in
local notation "MP" => M E B X → World E → Prop

section Shallow

/-- Forall-next: `p` holds now, the model can step, and `q` holds after every step. -/
def anc (p q : MP) (t : M E B X) (w : World E) : Prop :=
  p t w ∧ can_step t w ∧ ∀ t' w', ktrans t w t' w' → q t' w'

/-- Exists-next: `p` holds now and `q` holds after some step. -/
def enc (p q : MP) (t : M E B X) (w : World E) : Prop :=
  p t w ∧ ∃ t' w', ktrans t w t' w' ∧ q t' w'

/-- Forall strong until: the least fixpoint of `fun R => q ∨ anc p R` (inlined, since Lean rejects
the nested occurrence through `anc`). -/
inductive Auc (p q : MP) : MP
  | matchA {t w} : q t w → Auc p q t w
  | stepA {t w} : p t w → can_step t w → (∀ t' w', ktrans t w t' w' → Auc p q t' w') →
      Auc p q t w

/-- Exists strong until: the least fixpoint of `fun R => q ∨ enc p R`. -/
inductive Euc (p q : MP) : MP
  | matchE {t w} : q t w → Euc p q t w
  | stepE {t w} (t' w') : p t w → ktrans t w t' w' → Euc p q t' w' → Euc p q t w

variable {p p' q q' : MP} {t : M E B X} {w : World E}

/-- Rocq's `StepA` constructor. -/
theorem Auc.stepA' (h : anc p (Auc p q) t w) : Auc p q t w := .stepA h.1 h.2.1 h.2.2

/-- Rocq's `StepE` constructor. -/
theorem Euc.stepE' (h : enc p (Euc p q) t w) : Euc p q t w :=
  let ⟨hp, t', w', tr, h⟩ := h; .stepE t' w' hp tr h

theorem auc_unfold : Auc p q t w ↔ q t w ∨ anc p (Auc p q) t w :=
  ⟨fun | .matchA h => .inl h | .stepA hp hs hk => .inr ⟨hp, hs, hk⟩,
   fun | .inl h => .matchA h | .inr h => .stepA' h⟩

theorem euc_unfold : Euc p q t w ↔ q t w ∨ enc p (Euc p q) t w :=
  ⟨fun | .matchE h => .inl h | .stepE t' w' hp tr h => .inr ⟨hp, t', w', tr, h⟩,
   fun | .inl h => .matchE h | .inr h => .stepE' h⟩

/-- Rocq's custom induction scheme for `auc`. -/
theorem auc_ind (P : MP) (hbase : ∀ t w, q t w → P t w)
    (hstep : ∀ t w, anc p (Auc p q) t w → anc p P t w → P t w) :
    ∀ t w, Auc p q t w → P t w := by
  intro t w h
  induction h with
  | matchA h => exact hbase _ _ h
  | stepA hp hs hk ih => exact hstep _ _ ⟨hp, hs, hk⟩ ⟨hp, hs, ih⟩

/-- Rocq's custom induction scheme for `euc`. -/
theorem euc_ind (P : MP) (hbase : ∀ t w, q t w → P t w)
    (hstep : ∀ t w, (p t w ∧ ∃ t' w', ktrans t w t' w' ∧ Euc p q t' w' ∧ P t' w') → P t w) :
    ∀ t w, Euc p q t w → P t w := by
  intro t w h
  induction h with
  | matchE h => exact hbase _ _ h
  | stepE t' w' hp tr h ih => exact hstep _ _ ⟨hp, t', w', tr, h, ih⟩

/-- Next modality selected by its quantifier. -/
def qnext : Ticlq → MP → MP → MP
  | .A, p, r => anc p r
  | .E, p, r => enc p r

/-- Until modality selected by its quantifier. -/
def quntil : Ticlq → MP → MP → MP
  | .A, p, r => Auc p r
  | .E, p, r => Euc p r

@[simp] theorem qnext_A : qnext .A p q = anc p q := rfl
@[simp] theorem qnext_E : qnext .E p q = enc p q := rfl
@[simp] theorem quntil_A : quntil .A p q = Auc p q := rfl
@[simp] theorem quntil_E : quntil .E p q = Euc p q := rfl

/-- Map only the successor predicate, preserving prefix and progress. -/
theorem anc_mono_r (h : ∀ t w, q t w → q' t w) : ∀ t w, anc p q t w → anc p q' t w :=
  fun _ _ ⟨hp, hs, hk⟩ => ⟨hp, hs, fun t' w' tr => h _ _ (hk t' w' tr)⟩

/-- Map until leaves without changing its prefix or transition evidence. -/
theorem auc_mono_r (h : ∀ t w, q t w → q' t w) : ∀ t w, Auc p q t w → Auc p q' t w := by
  intro t w H
  induction H with
  | matchA hq => exact .matchA (h _ _ hq)
  | stepA hp hs _ ih => exact .stepA hp hs ih

theorem enc_mono_r (h : ∀ t w, q t w → q' t w) : ∀ t w, enc p q t w → enc p q' t w :=
  fun _ _ ⟨hp, t', w', tr, hq⟩ => ⟨hp, t', w', tr, h _ _ hq⟩

theorem euc_mono_r (h : ∀ t w, q t w → q' t w) : ∀ t w, Euc p q t w → Euc p q' t w := by
  intro t w H
  induction H with
  | matchE hq => exact .matchE (h _ _ hq)
  | stepE t' w' hp tr _ ih => exact .stepE t' w' hp tr ih

theorem euc_endpoint_exists (h : Euc p q t w) : ∃ u z, q u z := by
  induction h with
  | matchE hq => exact ⟨_, _, hq⟩
  | stepE _ _ _ _ _ ih => exact ih

/-- Weaken the guard while preserving the same finite endpoint. -/
theorem auc_mono_l (h : ∀ t w, p t w → p' t w) : ∀ t w, Auc p q t w → Auc p' q t w := by
  intro t w H
  induction H with
  | matchA hq => exact .matchA hq
  | stepA hp hs _ ih => exact .stepA (h _ _ hp) hs ih

theorem euc_mono_l (h : ∀ t w, p t w → p' t w) : ∀ t w, Euc p q t w → Euc p' q t w := by
  intro t w H
  induction H with
  | matchE hq => exact .matchE hq
  | stepE t' w' hp tr _ ih => exact .stepE t' w' (h _ _ hp) tr ih

/-- Flatten finite until segments with the same guard. -/
theorem auc_join : ∀ t w, Auc p (Auc p q) t w → Auc p q t w := by
  intro t w H
  induction H with
  | matchA hq => exact hq
  | stepA hp hs _ ih => exact .stepA hp hs ih

theorem euc_join : ∀ t w, Euc p (Euc p q) t w → Euc p q t w := by
  intro t w H
  induction H with
  | matchE hq => exact hq
  | stepE t' w' hp tr _ ih => exact .stepE t' w' hp tr ih

/-- The functor of the forall-always modality. -/
def agcF (p : MP) : Mon (Rel (M E B X) (World E)) where
  body := anc p
  mono h _ _ H := anc_mono_r (fun t w => h t w) _ _ H

/-- The functor of the exists-always modality. -/
def egcF (p : MP) : Mon (Rel (M E B X) (World E)) where
  body := enc p
  mono h _ _ H := enc_mono_r (fun t w => h t w) _ _ H

/-- Forall always: the greatest fixpoint of `anc p`. -/
abbrev agc (p : MP) : MP := gfp (agcF p)
/-- Exists always: the greatest fixpoint of `enc p`. -/
abbrev egc (p : MP) : MP := gfp (egcF p)

theorem agc_unfold : agc p t w ↔ anc p (agc p) t w :=
  ⟨fun h => gfp_pfp (b := agcF p) t w h, fun h => b_chain (gfp_chain (agcF p)) t w h⟩

theorem egc_unfold : egc p t w ↔ enc p (egc p) t w :=
  ⟨fun h => gfp_pfp (b := egcF p) t w h, fun h => b_chain (gfp_chain (egcF p)) t w h⟩

end Shallow

/-! ## Entailment -/

/-- Semantics of TICL formulas. -/
def entails : {i : Option (Type u)} → Ticl E i → M E B X → World E → Prop
  | _, .now p => fun _ w => p w ∧ NotDone w
  | _, .ret p => fun t w => ∃ x, p x w ∧ anc (fun _ w => NotDone w) (fun _ => DoneOf x w) t w
  | _, .cu .A p r => Auc (entails p) (entails r)
  | _, .cu .E p r => Euc (entails p) (entails r)
  | _, .cx .A p r => anc (entails p) (entails r)
  | _, .cx .E p r => enc (entails p) (entails r)
  | _, .cg .A p => agc (entails p)
  | _, .cg .E p => egc (entails p)
  | _, .and p r => fun t w => entails p t w ∧ entails r t w
  | _, .or p r => fun t w => entails p t w ∨ entails r t w

/-- Entailment of prefix formulas, with the model's return type explicit. -/
abbrev entailsL (X : Type u) (p : TiclL E) : M E B X → World E → Prop := entails p
/-- Entailment of formulas with a return postcondition. -/
abbrev entailsR (p : TiclR E X) : M E B X → World E → Prop := entails p

section Laws
variable {i : Option (Type u)} {t : M E B X} {w : World E}
open Notation

@[simp] theorem entails_cu_A (p : TiclL E) (r : Ticl E i) :
    entails (.cu .A p r) t w = Auc (entails p) (entails r) t w := rfl
@[simp] theorem entails_cu_E (p : TiclL E) (r : Ticl E i) :
    entails (.cu .E p r) t w = Euc (entails p) (entails r) t w := rfl
@[simp] theorem entails_cx_A (p : TiclL E) (r : Ticl E i) :
    entails (.cx .A p r) t w = anc (entails p) (entails r) t w := rfl
@[simp] theorem entails_cx_E (p : TiclL E) (r : Ticl E i) :
    entails (.cx .E p r) t w = enc (entails p) (entails r) t w := rfl
@[simp] theorem entails_cu (q : Ticlq) (p : TiclL E) (r : Ticl E i) :
    entails (.cu q p r) t w = quntil q (entails p) (entails r) t w := by cases q <;> rfl
@[simp] theorem entails_cx (q : Ticlq) (p : TiclL E) (r : Ticl E i) :
    entails (.cx q p r) t w = qnext q (entails p) (entails r) t w := by cases q <;> rfl

theorem ticl_now (p : World E → Prop) : entails (.now p) t w ↔ p w ∧ NotDone w := Iff.rfl

theorem ticl_pure : entails (pureₜ : TiclL E) t w ↔ w = .pure :=
  ⟨fun h => h.1, fun h => ⟨h, h ▸ .pure⟩⟩

theorem ticl_vis (p : (e : E.I) → E.O e → Prop) : entails (visₜ p) t w ↔ VisWith p w :=
  ⟨fun h => h.1, fun h => ⟨h, by cases h; constructor⟩⟩

theorem ticl_ret {Y : Type u} (p : Y → World E → Prop) :
    entails (.ret p) t w ↔ ∃ x, p x w ∧ anc (fun _ w => NotDone w) (fun _ => DoneOf x w) t w :=
  Iff.rfl

theorem ticl_an (p : TiclL E) (r : Ticl E i) :
    entails (.cx .A p r) t w ↔
      entails p t w ∧ can_step t w ∧ ∀ t' w', ktrans t w t' w' → entails r t' w' := Iff.rfl

theorem ticl_en (p : TiclL E) (r : Ticl E i) :
    entails (.cx .E p r) t w ↔ entails p t w ∧ ∃ t' w', ktrans t w t' w' ∧ entails r t' w' :=
  Iff.rfl

theorem ticl_au (p : TiclL E) (r : Ticl E i) :
    entails (.cu .A p r) t w ↔ Auc (entails p) (entails r) t w := Iff.rfl

theorem ticl_eu (p : TiclL E) (r : Ticl E i) :
    entails (.cu .E p r) t w ↔ Euc (entails p) (entails r) t w := Iff.rfl

@[simp] theorem ticl_and (p r : Ticl E i) :
    entails (.and p r) t w ↔ entails p t w ∧ entails r t w := Iff.rfl

@[simp] theorem ticl_or (p r : Ticl E i) :
    entails (.or p r) t w ↔ entails p t w ∨ entails r t w := Iff.rfl

theorem ticl_an_en {p : TiclL E} {r : Ticl E i} (h : entails (.cx .A p r) t w) :
    entails (.cx .E p r) t w :=
  let ⟨hp, ⟨t', w', tr⟩, hk⟩ := h; ⟨hp, t', w', tr, hk t' w' tr⟩

theorem ticl_au_eu {p : TiclL E} {r : Ticl E i} (h : entails (.cu .A p r) t w) :
    entails (.cu .E p r) t w := by
  change Auc _ _ t w at h
  induction h with
  | matchA h => exact .matchE h
  | stepA hp hs _ ih => obtain ⟨t', w', tr⟩ := hs; exact .stepE t' w' hp tr (ih t' w' tr)

theorem ticl_an_au {p : TiclL E} {r : Ticl E i} (h : entails (.cx .A p r) t w) :
    entails (.cu .A p r) t w :=
  let ⟨hp, hs, hk⟩ := h; .stepA hp hs fun t' w' tr => .matchA (hk t' w' tr)

theorem ticl_en_eu {p : TiclL E} {r : Ticl E i} (h : entails (.cx .E p r) t w) :
    entails (.cu .E p r) t w :=
  let ⟨hp, t', w', tr, hr⟩ := h; .stepE t' w' hp tr (.matchE hr)

theorem unfold_entails_ag (p : TiclL E) : entails (.cg .A p) t w = agc (entails p) t w := rfl
theorem unfold_entails_eg (p : TiclL E) : entails (.cg .E p) t w = egc (entails p) t w := rfl

theorem anc_not_done {p q : MP} (h : anc p q t w) : NotDone w := can_step_not_done h.2.1

theorem enc_not_done {p q : MP} (h : enc p q t w) : NotDone w :=
  let ⟨_, _, _, tr, _⟩ := h; ktrans_not_done tr

theorem ticl_not_done (φ : Ticl E i) (h : entails φ t w) : NotDone w := by
  induction φ generalizing t w with
  | now p => exact h.2
  | ret p => obtain ⟨_, _, h⟩ := h; exact anc_not_done h
  | cu q p r ihp ihr =>
    cases q
    · cases (h : Auc _ _ t w) with
      | matchA h => exact ihr h
      | stepA hp _ _ => exact ihp hp
    · cases (h : Euc _ _ t w) with
      | matchE h => exact ihr h
      | stepE _ _ hp _ _ => exact ihp hp
  | cx q p r ihp _ => cases q <;> exact ihp h.1
  | cg q p ihp =>
    cases q
    · exact ihp (agc_unfold.1 h).1
    · exact ihp (egc_unfold.1 h).1
  | and p r ihp _ => exact ihp h.1
  | or p r ihp ihr => exact h.elim ihp ihr

/-- Native return implies a terminal postcondition after its final transition, evaluated at the
unchanged predecessor world. -/
theorem ret_done_next (R : X → World E → Prop) (h : entails (.ret R) t w) :
    anc (entails (⊤ : TiclL E)) (fun _ wd => DoneWith R wd) t w := by
  obtain ⟨x, hR, hd, hs, hk⟩ := h
  refine ⟨⟨trivial, hd⟩, hs, fun t' w' tr => ?_⟩
  cases hk t' w' tr <;> constructor <;> exact hR

/-- Universal eventual native return includes the final value transition. -/
theorem af_ret_done (R : X → World E → Prop) (h : entails (AF (.ret R)) t w) :
    Auc (entails (⊤ : TiclL E)) (fun _ wd => DoneWith R wd) t w := by
  change Auc _ _ t w at h
  induction h with
  | matchA h =>
    obtain ⟨hp, hs, hk⟩ := ret_done_next R h
    exact .stepA hp hs fun t' w' tr => .matchA (hk t' w' tr)
  | stepA hp hs _ ih => exact .stepA hp hs ih

/-- Existential eventual native return includes one final value transition. -/
theorem ef_ret_done (R : X → World E → Prop) (h : entails (EF (.ret R)) t w) :
    Euc (entails (⊤ : TiclL E)) (fun _ wd => DoneWith R wd) t w := by
  change Euc _ _ t w at h
  induction h with
  | matchE h =>
    obtain ⟨hp, ⟨t', w', tr⟩, hk⟩ := ret_done_next R h
    exact .stepE t' w' hp tr (.matchE (hk t' w' tr))
  | stepE t' w' hp tr _ ih => exact .stepE t' w' hp tr ih

/-! ## Soundness of TICL formulas -/

/-- Bottom is false. -/
theorem ticll_sound : ¬ entails (⊥ : TiclL E) t w := fun h => h.1

/-- Prefix truth holds exactly at nonterminal worlds. -/
theorem ticll_top (h : NotDone w) : entails (⊤ : TiclL E) t w := ⟨trivial, h⟩

/-- No path eventually reaches bottom. -/
theorem ticll_sound_ef : ¬ entails (EF (⊥ : TiclL E)) t w := by
  intro h
  change Euc _ _ t w at h
  induction h with
  | matchE h => exact h.1
  | stepE _ _ _ _ _ ih => exact ih

theorem ticll_sound_af : ¬ entails (AF (⊥ : TiclL E)) t w :=
  fun h => ticll_sound_ef (ticl_au_eu h)

theorem ticlr_sound_ef : ¬ entails (EF (.ret fun (_ : X) (_ : World E) => False)) t w := by
  intro h
  change Euc _ _ t w at h
  induction h with
  | matchE h => obtain ⟨_, h, _⟩ := h; exact h
  | stepE _ _ _ _ _ ih => exact ih

theorem ticlr_sound_af : ¬ entails (AF (.ret fun (_ : X) (_ : World E) => False)) t w :=
  fun h => ticlr_sound_ef (ticl_au_eu h)

/-- Eventual terminal postconditions rule out infinite paths. -/
theorem af_done_accessible (R : X → World E → Prop)
    (h : Auc (entails (⊤ : TiclL E)) (fun _ wd => DoneWith R wd) t w) :
    Acc kripke_step (t, w) := by
  induction h with
  | matchA hd =>
    refine ⟨_, fun ⟨u, w'⟩ tr => ?_⟩
    have := ktrans_not_done tr
    cases hd <;> cases this
  | stepA _ _ _ ih => exact ⟨_, fun ⟨u, w'⟩ tr => ih u w' tr⟩

end Laws

-- Not ported: `entails_step`, `unfold_entails` (Lean's `entails` unfolds by `rfl`); the Ltac
-- `step`/`cinduction`/`coinduction_g` (use `agc_unfold`, `induction`, `coinduction`).

end Tisl
