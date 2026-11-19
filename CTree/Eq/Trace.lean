/- SPDX-License-Identifier: MIT -/
module

public import CTree.Eq.SBisim

/-!
# Traces

Coinductive traces of labels, the traces of a tree (`has_trace`), trace inclusion and trace
equivalence. Similarity implies trace inclusion and bisimilarity implies trace equivalence
(← `Eq/Trace.v`). `Trace E` is built with the vendored `Coinductive` polynomial-functor library,
like `CTree`.
-/

@[expose] public section
namespace CTree
open ITree (Effect)
open Coinductive (PF CoInd)
open Coinduction

/-- Base functor of traces. -/
inductive TraceF (E : Effect.{u}) (T : Type (u + 1)) : Type (u + 1)
  | nil
  | cons (l : Label E) (s : T)

/-- Shapes of `TraceF`. -/
inductive TraceF.In (E : Effect.{u}) : Type (u + 1)
  | nil
  | cons (l : Label E)

instance (E : Effect.{u}) : PF (TraceF E) where
  P := ⟨TraceF.In E, fun
    | .nil => PEmpty
    | .cons _ => PUnit⟩
  unpack
    | .nil => .obj .nil nofun
    | .cons l s => .obj (.cons l) fun _ => s
  pack
    | .obj .nil _ => .nil
    | .obj (.cons l) s => .cons l (s ⟨⟩)
  unpack_pack := by rintro _ (_|_) <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

/-- Possibly infinite sequences of labels. -/
abbrev Trace (E : Effect.{u}) : Type (u + 1) := CoInd (TraceF E)

variable {E C D : Effect.{u}} {X Y : Type u}

def Trace.nil : Trace E := CoInd.fold _ .nil
def Trace.cons (l : Label E) (s : Trace E) : Trace E := CoInd.fold _ (.cons l s)

@[simp] theorem Trace.unfold_nil : CoInd.unfold _ (Trace.nil : Trace E) = .nil :=
  Coinductive.unfold_fold _ _
@[simp] theorem Trace.unfold_cons (l : Label E) (s : Trace E) :
    CoInd.unfold _ (Trace.cons l s) = .cons l s :=
  Coinductive.unfold_fold _ _

theorem Trace.eq_nil_or_cons (s : Trace E) : s = .nil ∨ ∃ l s', s = .cons l s' := by
  rw [← Coinductive.fold_unfold _ s]
  cases CoInd.unfold _ s with
  | nil => exact .inl rfl
  | cons l s' => exact .inr ⟨l, s', rfl⟩

/-- The trace functor: `s` is a trace of `t` if its head is a transition of `t` whose target has
the tail of `s` as a trace. -/
def htr : Mon (Rel (Trace E) (CTree E C X)) where
  body R s t := match CoInd.unfold _ s with
    | .cons l s' => ∃ t', trans l t t' ∧ R s' t'
    | .nil => True
  mono h s _ := by
    dsimp only
    cases CoInd.unfold _ s with
    | nil => exact id
    | cons => exact fun ⟨t', h₁, h₂⟩ => ⟨t', h₁, h _ _ h₂⟩

def has_trace : Rel (Trace E) (CTree E C X) := gfp htr

/-- Every trace of `t` is a trace of `t'`. -/
def tracincl (t : CTree E C X) (t' : CTree E D Y) : Prop :=
  ∀ s, has_trace s t → has_trace s t'

/-- Trace equivalence. -/
def traceq (t : CTree E C X) (t' : CTree E D Y) : Prop := tracincl t t' ∧ tracincl t' t

section
variable {R : Rel (Trace E) (CTree E C X)} {t : CTree E C X}

@[simp] theorem htr_nil : htr R .nil t := by simp [htr]
@[simp] theorem htr_cons {l : Label E} {s : Trace E} :
    htr R (.cons l s) t ↔ ∃ t', trans l t t' ∧ R s t' := by
  simp [htr]

theorem has_trace_unfold {s : Trace E} : has_trace s t ↔ htr has_trace s t :=
  ⟨fun h => gfp_pfp (b := htr) s t h, fun h => b_chain (gfp_chain htr) s t h⟩

end

/-- Trace inclusion is weaker than similarity. -/
theorem ssim_tracincl {t : CTree E C X} {t' : CTree E D Y} (h : ssim Eq t t') : tracincl t t' := by
  intro s hs
  refine coinduction (b := htr)
    (fun i : {p : Trace E × CTree E C X × CTree E D Y // ssim Eq p.2.1 p.2.2 ∧ has_trace p.1 p.2.1}
      => i.1.1) (fun i => i.1.2.2) ?_ ⟨(s, t, t'), h, hs⟩
  rintro R - CIH ⟨⟨s, t, t'⟩, hss, hs⟩
  rcases Trace.eq_nil_or_cons s with rfl | ⟨l, s', rfl⟩
  · exact htr_nil
  · obtain ⟨t₁, ht₁, hs'⟩ := htr_cons.1 (has_trace_unfold.1 hs)
    obtain ⟨l', u', hu', hss', rfl⟩ := ssim_unfold.1 hss _ _ ht₁
    exact htr_cons.2 ⟨u', hu', CIH ⟨(s', t₁, u'), hss', hs'⟩⟩

/-- Trace equivalence is weaker than bisimilarity. -/
theorem sbisim_traceq {t t' : CTree E C X} (h : t ~ t') : traceq t t' :=
  ⟨ssim_tracincl (sbisim_ssim_subrelation_gen h), ssim_tracincl (sbisim_ssim_subrelation_gen (sbisim_symm h))⟩

end CTree
