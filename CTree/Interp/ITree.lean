/- SPDX-License-Identifier: MIT -/
module

public import CTree.Interp.Internalize
public import CTree.Eq.SBisim
public import ITree.InterpM

/-!
# Embedding interaction trees into choice trees

`embed'` interprets the events of an `ITree` as `CTree` events (its `tau`s become `guard`s, through
the guarded `CTree.iter`), and `embed` additionally internalizes the events of `C` as branches.
`embed_eutt` shows that `embed` maps `eutt`-equivalent itrees to strongly bisimilar ctrees
(← `Interp/ITree.v`).

The vendored `ITree` is extensional (`=` is Rocq's `eq_itree eq`), so the `Proper` instances
`embed_eq` and `eq_itree_productive` are not needed. It has no weak bisimulation, so `eutt` is
defined here with the coinduction tower: `EuttF` is the `eqitF` of the Rocq itree library with
both tau-stripping rules, and `eutt` its greatest fixpoint.
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect ITreeF)
open Coinduction

variable {E F C : Effect.{u}} {X : Type u}

/-- Each event is re-emitted as a `CTree` event. -/
def h_embed (e : E.I) : CTree E C (E.O e) := CTree.trigger e

/-- Interprets the events of an itree as ctree events. -/
def embed' (t : ITree.ITree E X) : CTree E B01 X := ITree.ITree.interpM h_embed t

/-- Embeds an itree into a ctree, internalizing the events of `C` as branches. -/
def embed (t : ITree.ITree (C ⊕ₑ E) X) : CTree E (B01 ⊕ₑ C) X := internalize (embed' t)

/-! ## Unfolding of `interpM` into `CTree` -/

theorem unfold_interp_ctree (f : (e : E.I) → CTree F C (E.O e)) (t : ITree.ITree E X) :
    ITree.ITree.interpM f t = match t.unfold with
      | .ret r => pure r
      | .tau t => .guard (ITree.ITree.interpM f t)
      | .vis e k => f e >>= fun x => .guard (ITree.ITree.interpM f (k x)) := by
  rw [ITree.ITree.interpM, iter_eq, unfold_iter]
  rcases t.unfold <;> simp

section
variable (f : (e : E.I) → CTree F C (E.O e))

@[simp] theorem interpM_ctree_ret (r : X) :
    ITree.ITree.interpM f (ITree.ITree.ret r : ITree.ITree E X) = pure r := by
  rw [unfold_interp_ctree, ITree.unfold_ret]

@[simp] theorem interpM_ctree_tau (t : ITree.ITree E X) :
    ITree.ITree.interpM f t.tau = .guard (ITree.ITree.interpM f t) := by
  rw [unfold_interp_ctree, ITree.unfold_tau]

@[simp] theorem interpM_ctree_vis (e : E.I) (k : E.O e → ITree.ITree E X) :
    ITree.ITree.interpM f (ITree.ITree.vis e k) =
      f e >>= fun x => .guard (ITree.ITree.interpM f (k x)) := by
  rw [unfold_interp_ctree, ITree.unfold_vis]

end

theorem unfold_embed (t : ITree.ITree (C ⊕ₑ E) X) :
    embed t = match t.unfold with
      | .ret r => pure r
      | .tau t => .guard (embed t)
      | .vis (.inl c) k => .brS' c fun x => .guard (.guard (embed (k x)))
      | .vis (.inr e) k => .vis e fun x => .guard (.guard (embed (k x))) := by
  rw [embed, embed', unfold_interp_ctree]
  rcases t.unfold with r | t | ⟨c | e, k⟩
  · exact internalize_ret r
  · simp [internalize, embed, embed']
  · simp [internalize, embed, embed', internalize_h', internalize_h, h_embed, CTree.trigger,
      CTree.branchS']
  · simp [internalize, embed, embed', internalize_h', h_embed, CTree.trigger]

/-! ## Transitions of embedded itrees -/

/-- The head of an itree is observable after finitely many `tau`s. Rocq's `productive`, renamed
since `CTree.Productive` exists. -/
inductive ITree.Productive : ITree.ITree E X → Prop
  | ret {r : X} {t} : t = ITree.ITree.ret r → ITree.Productive t
  | vis {e : E.I} {k : E.O e → ITree.ITree E X} {t} : t = ITree.ITree.vis e k → ITree.Productive t
  | tau {u t : ITree.ITree E X} : t = u.tau → ITree.Productive u → ITree.Productive t

theorem embed_trans_productive_aux {l : Label E} (T u : CTree E (B01 ⊕ₑ C) X)
    (t : ITree.ITree (C ⊕ₑ E) X) (ht : trans l T u) (h : T = embed t ∨ T = .guard (embed t)) :
    ITree.Productive t := by
  unfold trans at ht
  generalize hT : T.unfold = oT at ht
  induction ht generalizing T t with
  | br x _ ih =>
    rcases h with rfl | rfl
    · rw [unfold_embed] at hT
      rcases hu : t.unfold with r | t' | ⟨c | e, k⟩ <;> rw [hu] at hT <;> simp [CTree.brS', CTree.br'] at hT
      exact .vis (by rw [← ITree.ITree.unfold_fold t, hu]; rfl)
    · simp at hT
  | guard _ ih =>
    rcases h with rfl | rfl
    · rw [unfold_embed] at hT
      rcases hu : t.unfold with r | t' | ⟨c | e, k⟩ <;> rw [hu] at hT <;> simp [CTree.brS', CTree.br'] at hT
      exact .tau (by rw [← ITree.ITree.unfold_fold t, hu]; rfl) (ih _ t' (.inl rfl) (by rw [hT]))
    · simp at hT
      exact ih _ t (.inl rfl) (by rw [hT])
  | step =>
    rcases h with rfl | rfl
    · rw [unfold_embed] at hT
      rcases hu : t.unfold with r | t' | ⟨c | e, k⟩ <;> rw [hu] at hT <;> simp [CTree.brS', CTree.br'] at hT
    · simp at hT
  | obs =>
    rcases h with rfl | rfl
    · rw [unfold_embed] at hT
      rcases hu : t.unfold with r | t' | ⟨c | e, k⟩ <;> rw [hu] at hT <;> simp [CTree.brS', CTree.br'] at hT
      exact .vis (by rw [← ITree.ITree.unfold_fold t, hu]; rfl)
    · simp at hT
  | val =>
    rcases h with rfl | rfl
    · rw [unfold_embed] at hT
      rcases hu : t.unfold with r | t' | ⟨c | e, k⟩ <;> rw [hu] at hT <;> simp [CTree.brS', CTree.br'] at hT
      exact .ret (by rw [← ITree.ITree.unfold_fold t, hu]; rfl)
    · simp at hT

theorem embed_trans_productive {l : Label E} (t : ITree.ITree (C ⊕ₑ E) X)
    (u : CTree E (B01 ⊕ₑ C) X) (h : trans l (embed t) u) : ITree.Productive t :=
  embed_trans_productive_aux _ u t h (.inl rfl)

/-! ## Equivalence up to taus -/

section Eutt
variable {R₁ R₂ : Type u}

/-- One step of `eutt`: matching heads, with finitely many `tau`s stripped on either side. -/
inductive EuttF (RR : R₁ → R₂ → Prop) (sim : ITree.ITree E R₁ → ITree.ITree E R₂ → Prop) :
    ITreeF E R₁ (ITree.ITree E R₁) → ITreeF E R₂ (ITree.ITree E R₂) → Prop
  | ret {r₁ r₂} : RR r₁ r₂ → EuttF RR sim (.ret r₁) (.ret r₂)
  | tau {t₁ t₂} : sim t₁ t₂ → EuttF RR sim (.tau t₁) (.tau t₂)
  | vis {e k₁ k₂} : (∀ x, sim (k₁ x) (k₂ x)) → EuttF RR sim (.vis e k₁) (.vis e k₂)
  | tauL {t₁ ot₂} : EuttF RR sim t₁.unfold ot₂ → EuttF RR sim (.tau t₁) ot₂
  | tauR {ot₁ t₂} : EuttF RR sim ot₁ t₂.unfold → EuttF RR sim ot₁ (.tau t₂)

theorem EuttF.mono {RR : R₁ → R₂ → Prop} {sim sim' : ITree.ITree E R₁ → ITree.ITree E R₂ → Prop}
    (hs : ∀ a b, sim a b → sim' a b) {ot₁ ot₂} (h : EuttF RR sim ot₁ ot₂) :
    EuttF RR sim' ot₁ ot₂ := by
  induction h with
  | ret h => exact .ret h
  | tau h => exact .tau (hs _ _ h)
  | vis h => exact .vis fun x => hs _ _ (h x)
  | tauL _ ih => exact .tauL ih
  | tauR _ ih => exact .tauR ih

def euttB (RR : R₁ → R₂ → Prop) : Mon (Rel (ITree.ITree E R₁) (ITree.ITree E R₂)) where
  body sim t₁ t₂ := EuttF RR sim t₁.unfold t₂.unfold
  mono h _ _ H := EuttF.mono h H

/-- Equivalence up to taus (the `eutt` of the Rocq itree library). -/
def eutt (RR : R₁ → R₂ → Prop) : Rel (ITree.ITree E R₁) (ITree.ITree E R₂) := gfp (euttB RR)

variable {RR : R₁ → R₂ → Prop}

theorem eutt_unfold {t₁ : ITree.ITree E R₁} {t₂ : ITree.ITree E R₂} :
    eutt RR t₁ t₂ ↔ EuttF RR (eutt RR) t₁.unfold t₂.unfold :=
  ⟨fun h => gfp_pfp (b := euttB RR) t₁ t₂ h, fun h => b_chain (gfp_chain (euttB RR)) t₁ t₂ h⟩

/-- Rocq `eqit_inv_tauL`. -/
theorem eutt_inv_tauL {t₁ : ITree.ITree E R₁} {t₂ : ITree.ITree E R₂}
    (h : eutt RR t₁.tau t₂) : eutt RR t₁ t₂ := by
  rw [eutt_unfold, ITree.unfold_tau] at h
  refine eutt_unfold.2 ?_
  generalize ho : ITreeF.tau t₁ = ot at h
  generalize t₂.unfold = ot₂ at h
  induction h with
  | ret => cases ho
  | vis => cases ho
  | tau h => cases ho; exact .tauR (eutt_unfold.1 h)
  | tauL h => cases ho; exact h
  | tauR _ ih => exact .tauR (ih ho)

theorem eutt_sym {t₁ : ITree.ITree E R₁} {t₂ : ITree.ITree E R₂} (h : eutt RR t₁ t₂) :
    eutt (flip RR) t₂ t₁ := by
  refine coinduction (b := euttB (flip RR))
    (fun p : {p : ITree.ITree E R₁ × ITree.ITree E R₂ // eutt RR p.1 p.2} => p.1.2)
    (fun p => p.1.1) (fun R _ CIH ⟨⟨t₁, t₂⟩, h⟩ => ?_) ⟨(t₁, t₂), h⟩
  have CIH : ∀ a b, eutt RR a b → R b a := fun a b h => CIH ⟨(a, b), h⟩
  have h : EuttF RR (eutt RR) t₁.unfold t₂.unfold := eutt_unfold.1 h
  show EuttF (flip RR) R t₂.unfold t₁.unfold
  generalize t₁.unfold = o₁ at h ⊢
  generalize t₂.unfold = o₂ at h ⊢
  induction h with
  | ret h => exact .ret h
  | tau h => exact .tau (CIH _ _ h)
  | vis h => exact .vis fun x => CIH _ _ (h x)
  | tauL _ ih => exact .tauR ih
  | tauR _ ih => exact .tauL ih

end Eutt

/-- One direction of `embed_eutt`, for a chain element `R` containing the embedded `eutt`. -/
private theorem embed_eutt_ss {R : Rel (CTree E (B01 ⊕ₑ C) X) (CTree E (B01 ⊕ₑ C) X)}
    (hR : Chain (sb Eq) R) (CIH : ∀ t u, eutt Eq t u → R (embed t) (embed u))
    {t u : ITree.ITree (C ⊕ₑ E) X} (h : eutt Eq t u) : ss Eq R (embed t) (embed u) := by
  intro l T' ht
  have hgg (a : CTree E (B01 ⊕ₑ C) X) : CTree.guard (CTree.guard a) ~ a := sb_guard_l (sb_guard a)
  have step {t₁ t₂} (h : eutt Eq t₁ t₂) : R (embed t₁).guard.guard (embed t₂).guard.guard :=
    sbisim_clos_sb hR _ _ _ _ (hgg _) (CIH _ _ h) (sbisim_symm (hgg _))
  -- the right side may strip `tau`s before matching the left head
  have tauR {o : ITreeF (C ⊕ₑ E) X (ITree.ITree (C ⊕ₑ E) X)} (ho : ∀ t', o ≠ .tau t')
      (hP : ∀ u, EuttF Eq (eutt Eq) o u.unfold → (∀ u', u.unfold ≠ .tau u') →
        ∃ l' u', trans l' (embed u) u' ∧ R T' u' ∧ l = l') :
      ∀ u, EuttF Eq (eutt Eq) o u.unfold → ∃ l' u', trans l' (embed u) u' ∧ R T' u' ∧ l = l' := by
    intro u hu
    generalize hou : u.unfold = ou at hu
    induction hu generalizing u with
    | tauL => exact absurd rfl (ho _)
    | tau => exact absurd rfl (ho _)
    | tauR _ ih =>
      obtain ⟨l', u', h₁, h₂, h₃⟩ := ih ho hP _ rfl
      refine ⟨l', u', ?_, h₂, h₃⟩
      rw [unfold_embed, hou]
      exact trans_guard h₁
    | ret h => exact hP u (hou ▸ .ret h) fun _ h => by rw [hou] at h; cases h
    | vis h => exact hP u (hou ▸ .vis h) fun _ h => by rw [hou] at h; cases h
  induction embed_trans_productive t T' ht generalizing u with
  | ret e =>
    subst e
    rw [unfold_embed, ITree.unfold_ret] at ht
    obtain ⟨rfl, rfl⟩ := trans_ret_inv ht
    rw [eutt_unfold, ITree.unfold_ret] at h
    refine tauR (fun _ h => by cases h) (fun u hu hnt => ?_) u h
    rw [unfold_embed]
    generalize u.unfold = ou at hu hnt
    cases hu with
    | ret h => subst h; exact ⟨_, _, trans_ret _, sb_chain_refl (fun _ => rfl) hR _, rfl⟩
    | tauR => exact absurd rfl (hnt _)
  | @vis e k _ e' =>
    subst e'
    rw [unfold_embed, ITree.unfold_vis] at ht
    rw [eutt_unfold, ITree.unfold_vis] at h
    refine tauR (fun _ h => by cases h) (fun u hu hnt => ?_) u h
    rw [unfold_embed]
    generalize u.unfold = ou at hu hnt
    rcases e with c | e
    · obtain ⟨x, rfl, rfl⟩ := trans_brS'_inv ht
      cases hu with
      | vis h => exact ⟨_, _, trans_brS' _ x, step (h x), rfl⟩
      | tauR => exact absurd rfl (hnt _)
    · obtain ⟨x, rfl, rfl⟩ := trans_vis_inv ht
      cases hu with
      | vis h => exact ⟨_, _, trans_vis x _, step (h x), rfl⟩
      | tauR => exact absurd rfl (hnt _)
  | tau e _ ih =>
    subst e
    rw [unfold_embed, ITree.unfold_tau] at ht
    exact ih (eutt_inv_tauL h) (trans_guard_inv ht)

/-- `embed` maps `eutt`-equivalent itrees to strongly bisimilar ctrees. -/
theorem embed_eutt {t u : ITree.ITree (C ⊕ₑ E) X} (h : eutt Eq t u) : embed t ~ embed u := by
  refine coinduction (b := sb Eq)
    (fun p : {p : ITree.ITree (C ⊕ₑ E) X × ITree.ITree (C ⊕ₑ E) X // eutt Eq p.1 p.2} =>
      embed p.1.1) (fun p => embed p.1.2) (fun R hR CIH ⟨⟨t, u⟩, h⟩ => ?_) ⟨(t, u), h⟩
  have CIH : ∀ t u, eutt Eq t u → R (embed t) (embed u) := fun t u h => CIH ⟨(t, u), h⟩
  have hsym : eutt Eq u t := by
    have h' := eutt_sym h
    rwa [show flip (@Eq X) = Eq from funext fun _ => funext fun _ => propext eq_comm] at h'
  refine ⟨embed_eutt_ss hR CIH h, fun l u' hu => ?_⟩
  obtain ⟨l', t', h₁, h₂, rfl⟩ := embed_eutt_ss hR CIH hsym l u' hu
  exact ⟨l, t', h₁, sb_chain_symm (fun _ _ h => h.symm) hR _ _ h₂, rfl⟩

end CTree
