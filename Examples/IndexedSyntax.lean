/- SPDX-License-Identifier: MIT -/
module

public import Logic.Simulation
public import Logic.CTree.Sim
public import Logic.CTree.State
public import Logic.CTree.Soundness

/-!
# Indexed syntax regressions

Indexed prefix/suffix formula grammar, proof rules, judgment entry points and simulation transport
over abstract Kripke models and raw ctrees. Negative typing checks are `#guard_msgs`-wrapped
failing `example`s (← `examples/IndexedSyntax.v`).
-/

@[expose] public section
namespace Examples.IndexedSyntax
open CTree Tisl Tisl.Notation
open ITree (Effect)

/-- Rocq `cleft` on an until formula: its right operand holds now. -/
private theorem u_match {E B : Effect.{u}} {X : Type u} {i : Option (Type u)} {q : Ticlq}
    {φ : TiclL E} {ψ : Ticl E i} {t : CTree E B X} {w : World E} (h : entails ψ t w) :
    entails (.cu q φ ψ) t w := by
  cases q
  · exact .matchA h
  · exact .matchE h

section Grammar
variable {E : Effect.{0}} {X : Type} (P Q : World E → Prop) (R : X → World E → Prop)
  (p q : TiclL E) (r s : TiclR E X)

#check (Ticl.now P AU Ticl.now Q : TiclL E)
#check (p AU Ticl.ret R : TiclR E X)
#check ((p ∧ₜ AG q) AU (r ∨ₜ AX s) : TiclR E X)
#check (p AU q : TiclL E)

/--
error: Type mismatch
  Ticl.ret R
has type
  Ticl E (some X)
but is expected to have type
  TiclL E
-/
#guard_msgs in
example : TiclL E := Ticl.ret R

/--
error: Type mismatch
  Ticl.now fun x => True
has type
  Ticl ?m.1 none
but is expected to have type
  TiclR E X
-/
#guard_msgs in
example : TiclR E X := ⊤

/--
error: Application type mismatch: The argument
  r
has type
  TiclR E X
but is expected to have type
  Ticl E none
in the application
  Ticl.cu Ticlq.A r
-/
#guard_msgs in
example := r AU s

/--
error: Application type mismatch: The argument
  r
has type
  TiclR E X
but is expected to have type
  Ticl E none
in the application
  p ∧ₜ r
-/
#guard_msgs in
example := p ∧ₜ r

/--
error: Application type mismatch: The argument
  fun x x_1 => True
has type
  Bool → World E → Prop
but is expected to have type
  X → World E → Prop
in the application
  Ticl.ret fun x x_1 => True
-/
#guard_msgs in
example := Ticl.and r (Ticl.ret fun (_ : Bool) (_ : World E) => True)

/--
error: Application type mismatch: The argument
  p
has type
  TiclL E
but is expected to have type
  TiclR ?m.5 X
in the application
  contramap (fun x => x) p
-/
#guard_msgs in
example := contramap (fun x : X => x) p

/--
error: Application type mismatch: The argument
  r
has type
  TiclR E X
but is expected to have type
  TiclR ?m.5 Bool
in the application
  contramap (fun x => true) r
-/
#guard_msgs in
example := contramap (fun _ : Bool => true) r

theorem boolean_precedence : (p ∨ₜ q ∧ₜ p) = Ticl.and (Ticl.or p q) p := rfl

end Grammar

section SharedTactics
variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {E B : Effect.{u}} [Kripke M E B]
  {X : Type u} (t : M E B X) (w : World E) (b : Bool) (f g : TiclAt E X b)
  (p q : TiclL E) (r s : TiclR E X)

example : entails f t w → entails g t w → entails (.and f g) t w := fun hf hg => ⟨hf, hg⟩
example : entails (.and f g) t w → entails f t w := And.left
example : entailsR r t w → entailsR s t w → entailsR (r ∧ₜ s) t w := fun hr hs => ⟨hr, hs⟩
example : entailsL X (p ∧ₜ q) t w → entailsL X p t w := And.left
example : equiv_ticl M B X f g → entails f t w → entails g t w :=
  fun he hf => (equiv_ticl_entails he).1 hf
example : entails (.and f g) t w → True := fun _ => trivial

end SharedTactics

section AbstractMode
variable {E B : Effect.{u}} {X : Type u} (b : Bool) (t : CTree E B X) (w : World E)
  (phi : TiclL E) (psi : TiclAt E X b)

example : entails phi (CTree.step t) w → entails psi t w →
    entails (.cx .A phi psi) (CTree.step t) w :=
  fun hp hr => an_step.2 ⟨hp, hr⟩

example : entails phi (CTree.step t) w → entails (.cu .A phi psi) t w →
    entails (.cu .A phi psi) (CTree.step t) w :=
  fun hp hr => au_step.1 (.inr ⟨hp, hr⟩)

end AbstractMode

def changed_input : CTree void1 Bn Nat := pure 1
def changed_k : Nat → CTree void1 Bn Bool := fun _ => pure true

example : entails (.now fun _ => True : TiclL void1) (changed_input >>= changed_k) .pure :=
  ticl_bind_ret (R := fun n w => n = 1 ∧ w = .pure) (ret_ret .pure ⟨rfl, rfl⟩)
    fun _ _ ⟨_, hw⟩ => hw ▸ ⟨trivial, .pure⟩

example : entails (.ret fun x _ => x = true : TiclR void1 Bool) (changed_input >>= changed_k)
    .pure :=
  ticl_bind_ret (R := fun n w => n = 1 ∧ w = .pure) (ret_ret .pure ⟨rfl, rfl⟩)
    fun _ _ ⟨_, hw⟩ => hw ▸ ret_ret .pure rfl

theorem changed_until_prefix (q : Ticlq) :
    entails (.cu q (.now fun _ => True) (.now fun _ => True) : TiclL void1)
      (changed_input >>= changed_k) .pure :=
  u_bind_r (R := fun n w => n = 1 ∧ w = .pure) (u_match (ret_ret .pure ⟨rfl, rfl⟩))
    fun _ _ ⟨_, hw⟩ => u_match (hw ▸ ⟨trivial, .pure⟩)

theorem changed_until_suffix (q : Ticlq) :
    entails (.cu q (.now fun _ => True) (.ret fun x _ => x = true) : TiclR void1 Bool)
      (changed_input >>= changed_k) .pure :=
  u_bind_r (R := fun n w => n = 1 ∧ w = .pure) (u_match (ret_ret .pure ⟨rfl, rfl⟩))
    fun _ _ ⟨_, hw⟩ => u_match (hw ▸ ret_ret .pure rfl)

#check changed_until_prefix .A
#check changed_until_prefix .E
#check changed_until_suffix .A
#check changed_until_suffix .E

def countdown : Nat → CTree void1 Bn (Nat ⊕ Bool)
  | 0 => pure (.inr true)
  | n + 1 => .step (pure (.inl n))

theorem countdown_indexed (b : Bool) (p : TiclAt void1 Bool b)
    (Hexit : ∀ w, NotDone w → entails p (pure true : CTree void1 Bn Bool) w) (n : Nat) :
    entails (.cu .A (.now fun _ => True) p) (CTree.iter countdown n) .pure := by
  refine u_iter_nat (q := .A) (fun (_ : Nat) w => NotDone w) (fun n _ => n) .pure ?_
  intro s w hw
  cases s with
  | zero => exact .matchA (ret_ret hw (Hexit w hw))
  | succ s => exact au_step.1 (.inr ⟨⟨trivial, hw⟩, .matchA (ret_ret hw ⟨hw, Nat.lt_succ_self s⟩)⟩)

example (n : Nat) : entails (.cu .A (.now fun _ => True) (.ret fun x _ => x = true) :
    TiclR void1 Bool) (CTree.iter countdown n) .pure :=
  countdown_indexed true (.ret fun x _ => x = true) (fun _ hw => ret_ret hw rfl) n

example (n : Nat) : entails (.cu .A (.now fun _ => True) (.now fun _ => True) : TiclL void1)
    (CTree.iter countdown n) .pure :=
  countdown_indexed false (.now fun _ => True) (fun _ hw => ⟨trivial, hw⟩) n

section StateIndex
variable {E B : Effect.{u}} {S W X Y : Type u} (h : (e : E.I) → StateT S (ctreeW W B) (E.O e))
  (s : S) (b : Bool) (t : CTree E B Y) (k : Y → CTree E B X) (w : World (writerE W))
  (phi : TiclL (writerE W)) (psi : TiclAt (writerE W) (X × S) b)
  (R : Y → S → World (writerE W) → Prop)

example : entails (.cu .A phi (.ret fun (p : Y × S) => R p.1 p.2)) (interp_state h t s) w →
    (∀ y s' w', R y s' w' → entails (.cu .A phi psi) (interp_state h (k y) s') w') →
    entails (.cu .A phi psi) (interp_state h (t >>= k) s) w :=
  au_state_bind_r h

end StateIndex

def state_countdown : Nat → CTree (stateE Nat) Bn (Nat ⊕ Bool)
  | 0 => pure (.inr true)
  | k + 1 => CTree.put k >>= fun _ => pure (.inl k)

/-- One counting step is a log of the new state followed by the continuing return. -/
private theorem state_countdown_succ (n : Nat) :
    interp_state (h_stateW (B := Bn)) (state_countdown (n + 1)) (n + 1) ~
      (log n >>= fun _ => pure ((.inl n : Nat ⊕ Bool), n) :
        ctreeW Nat Bn ((Nat ⊕ Bool) × Nat)) := by
  rw [state_countdown, interp_state_bind]
  refine sbisim_trans (sbisim_clo_bind_eq (interp_state_put _ _) fun _ => sbisim_refl _) ?_
  simp
  exact sbisim_refl _

theorem state_countdown_indexed (b : Bool) (p : TiclAt (writerE Nat) (Bool × Nat) b)
    (Hexit : entails p (pure (true, 0) : ctreeW Nat Bn (Bool × Nat))
      (.obs (E := writerE Nat) (0 : Nat) ⟨⟩))
    (q : Ticlq) :
    entails (.cu q (.now fun _ => True) p) (instr_stateE (CTree.iter state_countdown 2) 2)
      .pure := by
  refine u_state_iter h_stateW
    (fun i s (w : World (writerE Nat)) =>
      s = i ∧ (i = 0 → w = .obs (E := writerE Nat) (0 : Nat) ⟨⟩))
    (InvImage (· < ·) fun p => p.1) (InvImage.wf _ Nat.lt_wfRel.wf) .pure ⟨rfl, nofun⟩ ?_
  rintro (_ | n) σ w hd ⟨rfl, hlast⟩
  · simp only [state_countdown, interp_state_ret]
    exact u_match (ret_ret hd (hlast rfl ▸ Hexit))
  · refine (proper_entails_meq _ (state_countdown_succ n)).2 ?_
    have hR : NotDone (.obs (E := writerE Nat) n ⟨⟩) ∧
        (n = n ∧ (n = 0 → World.obs (E := writerE Nat) n ⟨⟩ = .obs (E := writerE Nat) (0 : Nat) ⟨⟩))
        ∧ n < n + 1 :=
      ⟨.obs _ _, ⟨rfl, fun h => h ▸ rfl⟩, Nat.lt_succ_self n⟩
    cases q
    · exact af_log hd (u_match (ret_ret (.obs _ _) hR))
    · exact ef_log hd (u_match (ret_ret (.obs _ _) hR))

theorem state_countdown_suffix (q : Ticlq) :
    entails (.cu q (.now fun _ => True) (.ret fun result _ => result = (true, 0)) :
      TiclR (writerE Nat) (Bool × Nat)) (instr_stateE (CTree.iter state_countdown 2) 2) .pure :=
  state_countdown_indexed true _ (ret_ret (.obs _ _) rfl) q

theorem state_countdown_prefix (q : Ticlq) :
    entails (.cu q (.now fun _ => True) (visWₜ fun s => 0 = s) : TiclL (writerE Nat))
      (instr_stateE (CTree.iter state_countdown 2) 2) .pure :=
  state_countdown_indexed false _ ((ticl_vis _).2 (.obs _ _ rfl)) q

section Derivations
variable {E B : Effect.{u}} {X : Type u} (b : Bool) (t : CTree E B X) (w : World E)
  (phi : TiclL E) (psi : TiclAt E X b)

theorem derivation_guard : Syntails t w psi → Syntails (.guard t) w psi := .synGuard

theorem derivation_until_step : Syntails (CTree.step t) w phi → Syntails t w (.cu .A phi psi) →
    entails (.cu .A phi psi) (CTree.step t) w :=
  fun hp hs => soundness (.synAuStepL hp hs)

end Derivations

theorem derivation_now :
    Syntails (pure 1 : CTree void1 Bn Nat) .pure (.now fun _ => True) := .synNow trivial .pure

theorem derivation_ret :
    Syntails (pure 1 : CTree void1 Bn Nat) .pure (.ret fun n _ => n = 1) := .synRet rfl .pure

section Simulation
variable {E B : Effect.{u}} {X : Type u} (RV : X → X → Prop) (p : TiclL E) (r : TiclR E X)
  (t t' : CTree E B X) (w w' : World E)

theorem prefix_simulation : csim event_eq RV t t' → entails p t w → entails p t' w :=
  fun hsim hp => (framer_event_eq X false RV p t' w).1 <|
    ticl_csim false event_eq RV p trivial t t' w w hsim
      (simW_refl event_eq RV event_eq_refl w (ticl_not_done p hp)) hp

theorem suffix_simulation : (∀ x y1 y2, RV x y1 → RV x y2 → y1 = y2) →
    csim event_eq RV t t' → simW event_eq RV w w' → entails r t w →
    entails (framer X true event_eq RV r) t' w' :=
  fun hu hsim hw hr => ticl_csim true event_eq RV r ⟨event_eq_right_unique, hu⟩ t t' w w' hsim hw hr

end Simulation

section JudgmentEntrypoints
variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {E B : Effect.{u}} [Kripke M E B]
  {X Y : Type u} (t : M E B X) (u : M E B Y) (w : World E) (p q : TiclL E) (r s : TiclR E X)

def prefix_X : Prop := entailsL X p t w
def prefix_Y : Prop := entailsL Y p u w
def suffix_X : Prop := entailsR r t w
def prefix_domain_X : M E B X → World E → Prop := entailsL X p
def prefix_domain_Y : M E B Y → World E → Prop := entailsL Y p
def suffix_domain_X : M E B X → World E → Prop := entailsR r

/--
error: Application type mismatch: The argument
  r
has type
  TiclR E X
but is expected to have type
  TiclR E Y
in the application
  entailsR r
-/
#guard_msgs in
example : M E B Y → World E → Prop := entailsR r

#check entailsL X p
#check entailsL Y p
#check entailsR r

def truth_quote : Prop := entailsL X (⊤ : TiclL E) t w
def return_quote : Prop := entailsR (AX (Ticl.ret fun (_ : X) _ => True) : TiclR E X) t w

#check entailsL X p t w
#check entailsR r t w
#check entailsR ((p ∧ₜ AG q) AU (r ∨ₜ AX s)) t w

/--
error: Application type mismatch: The argument
  u
has type
  M E B Y
but is expected to have type
  ?m.1 E ?m.3 X
in the application
  entailsR r u
-/
#guard_msgs in
example : Prop := entailsR r u w

/--
error: Application type mismatch: The argument
  r
has type
  TiclR E X
but is expected to have type
  TiclL E
in the application
  entailsL X r
-/
#guard_msgs in
example : Prop := entailsL X r t w

/--
error: Application type mismatch: The argument
  p
has type
  TiclL E
but is expected to have type
  TiclR E X
in the application
  entailsR p
-/
#guard_msgs in
example : Prop := entailsR p t w

section Unknown
variable (i : Option (Type u)) (unknown : Ticl E i)

/--
error: Application type mismatch: The argument
  unknown
has type
  Ticl E i
but is expected to have type
  TiclL E
in the application
  entailsL X unknown
-/
#guard_msgs in
example : Prop := entailsL X unknown t w

/--
error: Application type mismatch: The argument
  unknown
has type
  Ticl E i
but is expected to have type
  TiclR E X
in the application
  entailsR unknown
-/
#guard_msgs in
example : Prop := entailsR unknown t w

end Unknown

-- Rocq `ticlr E (X -> False)`: `X → False` is a `Prop` in Lean, so the result type is `X → PEmpty`.
section Wrong
variable (wrong : TiclR E (X → PEmpty.{u + 1}))

/--
error: Application type mismatch: The argument
  t
has type
  M E B X
but is expected to have type
  ?m.1 E ?m.3 (X → PEmpty)
in the application
  entailsR wrong t
-/
#guard_msgs in
example : Prop := entailsR wrong t w

end Wrong

example : entailsL X p t w → entailsL X q t w → entailsL X (p ∧ₜ q) t w := fun hp hq => ⟨hp, hq⟩
example : entailsR r t w → entailsR s t w → entailsR (r ∧ₜ s) t w := fun hr hs => ⟨hr, hs⟩
example : entailsL X (p ∧ₜ q) t w → entailsL X p t w := And.left
example : entailsR (r ∧ₜ s) t w → entailsR r t w := And.left
example : entailsL X (p ∧ₜ q) t w → True := fun _ => trivial
example : entailsR (r ∧ₜ s) t w → True := fun _ => trivial

example : entailsL X p t w → entailsL X (p ∨ₜ q) t w := .inl
example : entailsL X q t w → entailsL X (p ∨ₜ q) t w := .inr
example : entailsR r t w → entailsR (r ∨ₜ s) t w := .inl
example : entailsR s t w → entailsR (r ∨ₜ s) t w := .inr
example : entailsL X (p ∨ₜ q) t w → entailsL X (q ∨ₜ p) t w := Or.symm
example : entailsR (r ∨ₜ s) t w → entailsR (s ∨ₜ r) t w := Or.symm

-- A variable path quantifier exercises both until branches; the index stays fixed by each tag.
example : ∀ z : Ticlq, entailsL X (.cu z p q) t w → NotDone w := fun _ h => ticl_not_done _ h
example : ∀ z : Ticlq, entailsR (.cu z p r) t w → NotDone w := fun _ h => ticl_not_done _ h

/-- Unfold one step of a global modality. -/
private theorem cg_now {z : Ticlq} (h : entailsL X (.cg z p) t w) : entailsL X p t w := by
  cases z
  · exact (agc_unfold.1 h).1
  · exact (egc_unfold.1 h).1

example : ∀ z : Ticlq, entailsL X (.cg z p) t w → entailsL X p t w := fun _ => cg_now t w p

-- Globals have prefix sort: a suffix consumer exposes its global guard with the next law.
example : ∀ z : Ticlq, entailsR (.cg z p AN r) t w → entailsL X p t w :=
  fun _ h => cg_now t w p ((ticl_an _ _).1 h).1

example : equiv_ticl M B X p q → entailsL X p t w → entailsL X q t w :=
  fun he hp => (equiv_ticl_entails he).1 hp
example : equiv_ticl M B X r s → entailsR r t w → entailsR s t w :=
  fun he hr => (equiv_ticl_entails he).1 hr

section Mode
variable (b : Bool) (f g : TiclAt E X b)

#check entails f t w
example : entails f t w → entails (.or f g) t w := .inl
example : entails g t w → entails (.or f g) t w := .inr
example : entails (.or f g) t w → entails (.or g f) t w := Or.symm
example : ∀ z : Ticlq, entails (.cu z p f) t w → NotDone w := fun _ h => ticl_not_done _ h
example : ∀ z : Ticlq, entails (.cx .A (.cg z p) f) t w → entails p t w :=
  fun _ h => cg_now t w p ((ticl_an _ _).1 h).1

end Mode

end JudgmentEntrypoints

section EntrypointModelRewriting
variable {M : Effect.{u} → Effect.{u} → Type u → Type u} {E B : Effect.{u}} [Kripke M E B]
  {X : Type u} {meq : M E B X → M E B X → Prop} [KripkeSetoid M E B X meq]
  (t u : M E B X) (w : World E) (p : TiclL E) (r : TiclR E X)

example : meq t u → (entailsL X p t w ↔ entailsL X p u w) := proper_entails_meq p
example : meq t u → (entailsR r t w ↔ entailsR r u w) := proper_entails_meq r

end EntrypointModelRewriting

section EntrypointCTreeRewriting
variable {E B : Effect.{u}} {X : Type u} (t : CTree E B X) (w : World E) (p : TiclL E)
  (r : TiclR E X)

example : entailsL X p (CTree.guard t) w ↔ entailsL X p t w := proper_entails_meq p (sb_guard t)
example : entailsR r (CTree.guard t) w ↔ entailsR r t w := proper_entails_meq r (sb_guard t)

end EntrypointCTreeRewriting

/-- A bare logger must inhabit the logical model's result universe, not only the universe of the
event reply. -/
theorem log_native_return {S : Type u} {B : Effect.{u}} (s : S) :
    entailsR (AX (Ticl.ret fun result w => result = ⟨⟩ ∧ w = .obs (E := writerE S) s ⟨⟩))
      (log (B := B) s) .pure := by
  unfold log
  exact (an_vis (E := writerE S) (e := s) ⟨⟩).2
    ⟨⟨trivial, .pure⟩, fun _ => ret_ret (.obs _ _) ⟨rfl, rfl⟩⟩

section ReturnMapping
variable {E : Effect.{0}}

#check (rfl : TiclL E = Ticl E none)
#check (rfl : TiclR E Nat = Ticl E (some Nat))

def mapped_source : TiclR E Nat := .cu .A (.now fun _ => True) (.ret fun n _ => n = 1)

theorem return_mapping :
    contramap (fun b : Bool => if b then 1 else 0) (mapped_source (E := E)) =
      .cu .A (.now fun _ => True) (.ret fun (b : Bool) _ => (if b then 1 else 0) = 1) := rfl

end ReturnMapping

-- Not ported: module `StoreExtension` (`x`, five `Check`s of StImp state notation) and module
-- `HeapExtension` (`x`, two `Check`s of HeapImp notation): Lang.StImp/HeapImp not ported.
-- `Show.` commands inside proofs (proof-state display, no Lean counterpart).

end Examples.IndexedSyntax
