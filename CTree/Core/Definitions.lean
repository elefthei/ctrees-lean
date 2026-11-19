/- SPDX-License-Identifier: MIT -/
module

public import Coinductive
public import ITree.Effect
public import ITree.InterpM
public import CTree.Core.Utils
public import CTree.Core.Index

/-!
# Choice trees

A choice tree `CTree E B R` is a possibly infinite tree whose nodes are
- `ret r`: a pure computation returning `r`,
- `stuck`: a deadlocked computation,
- `step t`: an observable internal step,
- `guard t`: an unobservable internal step,
- `vis e k`: an external event `e : E.I` continuing with `k`,
- `br c k`: an internal non-deterministic branching over the branches of `c : B.I`.

The type is the final coalgebra of the polynomial functor `CTreeF E B R`; corecursive functions are
defined by `partial_fixpoint` (← `Core/CTreeDefinitions.v`).
-/

@[expose] public section
namespace CTree
open Coinductive Lean.Order
open ITree (Effect Subeffect)

inductive CTreeF (E B : Effect.{u}) (R : Type u) (X : Type u) : Type u where
  | ret (r : R)
  | stuck
  | step (t : X)
  | guard (t : X)
  | vis (e : E.I) (k : E.O e → X)
  | br (c : B.I) (k : B.O c → X)

inductive CTreeF.In (E B : Effect.{u}) (R : Type u) : Type u where
  | ret (r : R)
  | stuck
  | step
  | guard
  | vis (e : E.I)
  | br (c : B.I)

instance (E B : Effect.{u}) (R : Type u) : PF (CTreeF E B R) where
  P := ⟨CTreeF.In E B R, fun
    | .ret _ => PEmpty
    | .stuck => PEmpty
    | .step => PUnit
    | .guard => PUnit
    | .vis e => E.O e
    | .br c => B.O c⟩
  unpack
    | .ret r => .obj (.ret r) nofun
    | .stuck => .obj .stuck nofun
    | .step t => .obj .step fun _ => t
    | .guard t => .obj .guard fun _ => t
    | .vis e k => .obj (.vis e) k
    | .br c k => .obj (.br c) k
  pack
    | .obj (.ret r) _ => .ret r
    | .obj .stuck _ => .stuck
    | .obj .step k => .step (k ⟨⟩)
    | .obj .guard k => .guard (k ⟨⟩)
    | .obj (.vis e) k => .vis e k
    | .obj (.br c) k => .br c k
  unpack_pack := by rintro _ ⟨⟩ <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

abbrev CTree (E B : Effect.{u}) (R : Type u) : Type u := CoInd (CTreeF E B R)

variable {E B : Effect.{u}} {R S : Type u}

def CTree.fold (t : CTreeF E B R (CTree E B R)) : CTree E B R := CoInd.fold _ t
def CTree.unfold (t : CTree E B R) : CTreeF E B R (CTree E B R) := CoInd.unfold _ t
def CTree.ret (r : R) : CTree E B R := .fold (.ret r)
def CTree.stuck : CTree E B R := .fold .stuck
def CTree.step (t : CTree E B R) : CTree E B R := .fold (.step t)
def CTree.guard (t : CTree E B R) : CTree E B R := .fold (.guard t)
def CTree.vis (e : E.I) (k : E.O e → CTree E B R) : CTree E B R := .fold (.vis e k)
def CTree.br (c : B.I) (k : B.O c → CTree E B R) : CTree E B R := .fold (.br c k)
/-- A branching whose every branch first takes an observable step. -/
def CTree.brS (c : B.I) (k : B.O c → CTree E B R) : CTree E B R := .br c fun x => .step (k x)

/-- The bottom element of the approximation order is `spin` (`guard` forever). -/
instance : Inhabited (CTreeF E B R PUnit) where default := .guard ⟨⟩

/-! ## Unfolding and injectivity -/

@[simp]
theorem fold_unfold (t : CTree E B R) : CTree.fold t.unfold = t := by
  simp [CTree.fold, CTree.unfold]

@[simp]
theorem unfold_fold (t : CTreeF E B R (CTree E B R)) : (CTree.fold t).unfold = t := by
  simp [CTree.fold, CTree.unfold]

@[simp]
theorem fold_eq_fold_iff {x y : CTreeF E B R (CTree E B R)} : CTree.fold x = CTree.fold y ↔ x = y :=
  ⟨fun h => by simpa using congrArg CTree.unfold h, fun h => h ▸ rfl⟩

theorem unfold_inj {t u : CTree E B R} (h : t.unfold = u.unfold) : t = u := by
  rw [← fold_unfold t, ← fold_unfold u, h]

@[simp] theorem unfold_ret (r : R) : (CTree.ret r : CTree E B R).unfold = .ret r := unfold_fold _
@[simp] theorem unfold_stuck : (CTree.stuck : CTree E B R).unfold = .stuck := unfold_fold _
@[simp] theorem unfold_step (t : CTree E B R) : t.step.unfold = .step t := unfold_fold _
@[simp] theorem unfold_guard (t : CTree E B R) : t.guard.unfold = .guard t := unfold_fold _
@[simp] theorem unfold_vis (e : E.I) (k : E.O e → CTree E B R) :
    (CTree.vis e k).unfold = .vis e k := unfold_fold _
@[simp] theorem unfold_br (c : B.I) (k : B.O c → CTree E B R) :
    (CTree.br c k).unfold = .br c k := unfold_fold _

theorem brS_eq (c : B.I) (k : B.O c → CTree E B R) :
    CTree.brS c k = .br c fun x => .step (k x) := rfl

@[simp] theorem unfold_brS (c : B.I) (k : B.O c → CTree E B R) :
    (CTree.brS c k).unfold = .br c fun x => .step (k x) := unfold_fold _

@[simp] theorem fold_ret (r : R) : CTree.fold (.ret r) = (CTree.ret r : CTree E B R) := rfl
@[simp] theorem fold_stuck : CTree.fold .stuck = (CTree.stuck : CTree E B R) := rfl
@[simp] theorem fold_step (t : CTree E B R) : CTree.fold (.step t) = t.step := rfl
@[simp] theorem fold_guard (t : CTree E B R) : CTree.fold (.guard t) = t.guard := rfl
@[simp] theorem fold_vis (e : E.I) (k : E.O e → CTree E B R) :
    CTree.fold (.vis e k) = CTree.vis e k := rfl
@[simp] theorem fold_br (c : B.I) (k : B.O c → CTree E B R) :
    CTree.fold (.br c k) = CTree.br c k := rfl

@[simp] theorem ret_eq_ret_iff {r s : R} : (CTree.ret r : CTree E B R) = .ret s ↔ r = s :=
  ⟨fun h => by simpa using congrArg CTree.unfold h, by rintro rfl; rfl⟩
@[simp] theorem step_eq_step_iff {t u : CTree E B R} : t.step = u.step ↔ t = u :=
  ⟨fun h => by simpa using congrArg CTree.unfold h, by rintro rfl; rfl⟩
@[simp] theorem guard_eq_guard_iff {t u : CTree E B R} : t.guard = u.guard ↔ t = u :=
  ⟨fun h => by simpa using congrArg CTree.unfold h, by rintro rfl; rfl⟩
@[simp] theorem vis_eq_vis_iff {e : E.I} {k₁ k₂ : E.O e → CTree E B R} :
    CTree.vis e k₁ = .vis e k₂ ↔ k₁ = k₂ :=
  ⟨fun h => by simpa using congrArg CTree.unfold h, by rintro rfl; rfl⟩
@[simp] theorem br_eq_br_iff {c : B.I} {k₁ k₂ : B.O c → CTree E B R} :
    CTree.br c k₁ = .br c k₂ ↔ k₁ = k₂ :=
  ⟨fun h => by simpa using congrArg CTree.unfold h, by rintro rfl; rfl⟩

/-! ## Approximations -/

@[simp]
theorem ret_approx_1 (r : R) n : (CTree.ret r : CTree E B R).approx (n + 1) = CTreeF.ret r := by
  simp [CTree.ret, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_ret_approx_1 (r : R) n :
    (CTree.fold (.ret r : CTreeF E B R _)).approx (n + 1) = CTreeF.ret r := ret_approx_1 r n

@[simp]
theorem stuck_approx_1 n : (CTree.stuck : CTree E B R).approx (n + 1) = CTreeF.stuck := by
  simp [CTree.stuck, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_stuck_approx_1 n :
    (CTree.fold (.stuck : CTreeF E B R _)).approx (n + 1) = CTreeF.stuck := stuck_approx_1 n

@[simp]
theorem step_approx_1 (t : CTree E B R) n : t.step.approx (n + 1) = CTreeF.step (t.approx n) := by
  simp [CTree.step, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_step_approx_1 (t : CTree E B R) n :
    (CTree.fold (.step t)).approx (n + 1) = CTreeF.step (t.approx n) := step_approx_1 t n

@[simp]
theorem guard_approx_1 (t : CTree E B R) n :
    t.guard.approx (n + 1) = CTreeF.guard (t.approx n) := by
  simp [CTree.guard, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_guard_approx_1 (t : CTree E B R) n :
    (CTree.fold (.guard t)).approx (n + 1) = CTreeF.guard (t.approx n) := guard_approx_1 t n

@[simp]
theorem vis_approx_1 e (k : E.O e → CTree E B R) n :
    (CTree.vis e k).approx (n + 1) = CTreeF.vis e (fun o => (k o).approx n) := by
  simp [CTree.vis, CTree.fold, CoInd.fold, PF.map, PF.pack]
  rfl

@[simp]
theorem fold_vis_approx_1 e (k : E.O e → CTree E B R) n :
    (CTree.fold (.vis e k)).approx (n + 1) = CTreeF.vis e (fun o => (k o).approx n) :=
  vis_approx_1 e k n

@[simp]
theorem br_approx_1 c (k : B.O c → CTree E B R) n :
    (CTree.br c k).approx (n + 1) = CTreeF.br c (fun o => (k o).approx n) := by
  simp [CTree.br, CTree.fold, CoInd.fold, PF.map, PF.pack]
  rfl

@[simp]
theorem fold_br_approx_1 c (k : B.O c → CTree E B R) n :
    (CTree.fold (.br c k)).approx (n + 1) = CTreeF.br c (fun o => (k o).approx n) :=
  br_approx_1 c k n

/-! ## Monotonicity of the constructors -/

theorem step_monoN (t1 t2 : CTree E B R) n :
    CoIndN.le _ (t1.approx n) (t2.approx n) →
    CoIndN.le _ (t1.step.approx (n + 1)) (t2.step.approx (n + 1)) := by
  intro hs
  simp [CoIndN.le, PF.unpack]
  right
  constructor <;> try rfl
  grind [coherent1]

@[partial_fixpoint_monotone]
theorem step_mono α [PartialOrder α] (f : α → CTree E B R) :
    monotone f → monotone (fun x => CTree.step (f x)) := by
  intro hf t1 t2 hle
  apply CoInd.le_leN
  rintro ⟨n⟩; simp [CoIndN.le]
  apply step_monoN
  grind [CoInd.leN_le, monotone]

theorem guard_monoN (t1 t2 : CTree E B R) n :
    CoIndN.le _ (t1.approx n) (t2.approx n) →
    CoIndN.le _ (t1.guard.approx (n + 1)) (t2.guard.approx (n + 1)) := by
  intro hs
  simp [CoIndN.le, PF.unpack]
  right
  constructor <;> try rfl
  grind [coherent1]

@[partial_fixpoint_monotone]
theorem guard_mono α [PartialOrder α] (f : α → CTree E B R) :
    monotone f → monotone (fun x => CTree.guard (f x)) := by
  intro hf t1 t2 hle
  apply CoInd.le_leN
  rintro ⟨n⟩; simp [CoIndN.le]
  apply guard_monoN
  grind [CoInd.leN_le, monotone]

theorem vis_monoN e (k1 k2 : E.O e → CTree E B R) n :
    (∀ o, CoIndN.le _ ((k1 o).approx n) ((k2 o).approx n)) →
    CoIndN.le _ ((CTree.vis e k1).approx (n + 1)) ((CTree.vis e k2).approx (n + 1)) := by
  intro hs
  simp [CoIndN.le, PF.unpack]
  right
  constructor <;> try rfl
  grind [coherent1]

@[partial_fixpoint_monotone]
theorem vis_mono α [PartialOrder α] e (f : α → E.O e → CTree E B R) :
    monotone f → monotone (fun x => CTree.vis e (f x)) := by
  intro hf t1 t2 hle
  apply CoInd.le_leN
  rintro ⟨n⟩; simp [CoIndN.le]
  apply vis_monoN
  intro o
  have := hf t1 t2 hle o
  grind [CoInd.leN_le]

theorem br_monoN c (k1 k2 : B.O c → CTree E B R) n :
    (∀ o, CoIndN.le _ ((k1 o).approx n) ((k2 o).approx n)) →
    CoIndN.le _ ((CTree.br c k1).approx (n + 1)) ((CTree.br c k2).approx (n + 1)) := by
  intro hs
  simp [CoIndN.le, PF.unpack]
  right
  constructor <;> try rfl
  grind [coherent1]

@[partial_fixpoint_monotone]
theorem br_mono α [PartialOrder α] c (f : α → B.O c → CTree E B R) :
    monotone f → monotone (fun x => CTree.br c (f x)) := by
  intro hf t1 t2 hle
  apply CoInd.le_leN
  rintro ⟨n⟩; simp [CoIndN.le]
  apply br_monoN
  intro o
  have := hf t1 t2 hle o
  grind [CoInd.leN_le]

/-! ## Divergence and the approximation order -/

/-- Silent divergence: `guard` forever. -/
def CTree.spin : CTree E B R := spin.guard
partial_fixpoint

@[simp]
theorem bot_eq : CoInd.bot (CTreeF E B R) = CTree.spin := by
  ext n
  induction n; congr 0
  rw [CoInd.bot_eq, CTree.spin]
  simp [PF.map, PF.pack, CoInd.fold, *, PF.unpack, default]

theorem le_unfold (t1 t2 : CTree E B R) :
    (t1 ⊑ t2) = (t1 = .spin ∨
      (∃ r, t1 = .ret r ∧ t2 = .ret r) ∨
      (t1 = .stuck ∧ t2 = .stuck) ∨
      (∃ t1' t2', t1 = .step t1' ∧ t2 = .step t2' ∧ t1' ⊑ t2') ∨
      (∃ t1' t2', t1 = .guard t1' ∧ t2 = .guard t2' ∧ t1' ⊑ t2') ∨
      (∃ e k1 k2, t1 = .vis e k1 ∧ t2 = .vis e k2 ∧ ∀ o, k1 o ⊑ k2 o) ∨
      (∃ c k1 k2, t1 = .br c k1 ∧ t2 = .br c k2 ∧ ∀ o, k1 o ⊑ k2 o)) := by
  ext
  constructor
  · intro h
    rw [CoInd.le_unfold] at h
    rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp
    rw [← Coinductive.fold_unfold _ t1, ← Coinductive.fold_unfold _ t2]
    rw [← PF.unpack_pack (CoInd.unfold _ t1), ← PF.unpack_pack (CoInd.unfold _ t2)]
    simp only [h1, h2]
    right
    cases i <;> simp [PF.pack, CTree.ret, CTree.stuck, CTree.step, CTree.guard, CTree.vis,
      CTree.br, CTree.fold] <;> grind
  · rintro (rfl|⟨_, rfl, rfl⟩|⟨rfl, rfl⟩|⟨_, _, rfl, rfl, _⟩|⟨_, _, rfl, rfl, _⟩|
      ⟨_, _, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
    · simp [CoInd.le_unfold]
    · apply PartialOrder.rel_refl
    · apply PartialOrder.rel_refl
    all_goals
      simp [CoInd.le_unfold]
      right
      simp [PF.unpack, CTree.step, CTree.guard, CTree.vis, CTree.br, CTree.fold]
      constructor <;> try rfl
      grind

/-! ## Monadic structure -/

/-- Monadic composition, tree substitution, sequencing of computations. Use `>>=` instead. -/
def CTree.bind (t : CTree E B R) (k : R → CTree E B S) : CTree E B S :=
  match t.unfold with
  | .ret r => k r
  | .stuck => .stuck
  | .step t => .step (CTree.bind t k)
  | .guard t => .guard (CTree.bind t k)
  | .vis e h => .vis e fun x => CTree.bind (h x) k
  | .br c h => .br c fun x => CTree.bind (h x) k
partial_fixpoint

theorem bind_unfold (t : CTree E B R) (k : R → CTree E B S) :
    CTree.bind t k = match t.unfold with
      | .ret r => k r
      | .stuck => .stuck
      | .step t => .step (CTree.bind t k)
      | .guard t => .guard (CTree.bind t k)
      | .vis e h => .vis e fun x => CTree.bind (h x) k
      | .br c h => .br c fun x => CTree.bind (h x) k := by
  rw [CTree.bind]

theorem unfold_spin : (CTree.spin : CTree E B R) = .guard .spin := by
  rw (occs := .pos [1]) [CTree.spin]

@[simp] theorem spin_unfold : (CTree.spin : CTree E B R).unfold = .guard .spin := by
  rw (occs := .pos [1]) [unfold_spin]; simp

theorem spin_bind' (k : R → CTree E B S) : CTree.bind .spin k = .spin := by
  ext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bind_unfold, spin_unfold]
    conv => rhs; rw [unfold_spin]
    simp [ih]

@[partial_fixpoint_monotone]
theorem bind_mono {α} [PartialOrder α] (f : α → CTree E B R) (g : α → R → CTree E B S) :
    monotone f → monotone g → monotone (fun x => CTree.bind (f x) (g x)) := by
  intro hf hg t1 t2 hle
  apply CoInd.le_leN
  intro n
  dsimp only
  have hlef : (f t1) ⊑ (f t2) := by apply hf; assumption
  generalize f t1 = t1, f t2 = t2 at hlef
  induction n generalizing t1 t2; simp [CoIndN.le]
  rw [le_unfold] at hlef
  rcases hlef with (rfl|⟨_, rfl, rfl⟩|⟨rfl, rfl⟩|⟨_, _, rfl, rfl, _⟩|⟨_, _, rfl, rfl, _⟩|
    ⟨_, _, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
  · rw [spin_bind']
    simp [CoIndN.le, CoIndN.bot]
  all_goals unfold CTree.bind
  · rename_i x
    simp
    have := hg t1 t2 hle x
    grind [CoInd.leN_le, monotone]
  · simp [CoIndN.le, PF.unpack]
    right
    exact .single _ _ _ _ _ rfl rfl nofun
  · simp
    apply step_monoN
    grind [CoInd.leN_le, monotone]
  · simp
    apply guard_monoN
    grind [CoInd.leN_le, monotone]
  · simp
    apply vis_monoN
    grind [CoInd.leN_le, monotone]
  · simp
    apply br_monoN
    grind [CoInd.leN_le, monotone]

instance : Monad (CTree E B) where
  pure := CTree.ret
  bind := CTree.bind

@[simp] theorem ret_eq_pure (r : R) : (CTree.ret r : CTree E B R) = pure r := rfl
@[simp] theorem bind_eq (t : CTree E B R) (k : R → CTree E B S) : CTree.bind t k = t >>= k := rfl

@[simp] theorem unfold_pure (r : R) : (pure r : CTree E B R).unfold = .ret r := unfold_ret r

@[simp]
theorem pure_approx_1 (r : R) n : (pure r : CTree E B R).approx (n + 1) = CTreeF.ret r :=
  ret_approx_1 r n

theorem bind_def (t : CTree E B R) (k : R → CTree E B S) :
    t >>= k = match t.unfold with
      | .ret r => k r
      | .stuck => .stuck
      | .step t => .step (t >>= k)
      | .guard t => .guard (t >>= k)
      | .vis e h => .vis e fun x => h x >>= k
      | .br c h => .br c fun x => h x >>= k :=
  bind_unfold t k

theorem unfold_bind (t : CTree E B R) (k : R → CTree E B S) :
    (t >>= k).unfold = match t.unfold with
      | .ret r => (k r).unfold
      | .stuck => .stuck
      | .step t => .step (t >>= k)
      | .guard t => .guard (t >>= k)
      | .vis e h => .vis e fun x => h x >>= k
      | .br c h => .br c fun x => h x >>= k := by
  rw [bind_def]; split <;> simp

@[elab_as_elim, cases_eliminator]
def CTree.cases {motive : CTree E B R → Sort v}
    (ret : ∀ r, motive (pure r))
    (stuck : motive .stuck)
    (step : ∀ t, motive (.step t))
    (guard : ∀ t, motive (.guard t))
    (vis : ∀ e k, motive (.vis e k))
    (br : ∀ c k, motive (.br c k))
    (t : CTree E B R) : motive t := by
  rw [← fold_unfold t]
  cases t.unfold
  · apply ret
  · apply stuck
  · apply step
  · apply guard
  · apply vis
  · apply br

@[simp] theorem pure_bind' (r : R) (k : R → CTree E B S) : pure r >>= k = k r := by
  rw [bind_def]; simp
@[simp] theorem stuck_bind (k : R → CTree E B S) : (CTree.stuck : CTree E B R) >>= k = .stuck := by
  rw [bind_def]; simp
@[simp] theorem step_bind (t : CTree E B R) (k : R → CTree E B S) :
    t.step >>= k = .step (t >>= k) := by
  rw [bind_def]; simp
@[simp] theorem guard_bind (t : CTree E B R) (k : R → CTree E B S) :
    t.guard >>= k = .guard (t >>= k) := by
  rw [bind_def]; simp
@[simp] theorem vis_bind (e : E.I) (h : E.O e → CTree E B R) (k : R → CTree E B S) :
    CTree.vis e h >>= k = .vis e fun x => h x >>= k := by
  rw [bind_def]; simp
@[simp] theorem br_bind (c : B.I) (h : B.O c → CTree E B R) (k : R → CTree E B S) :
    CTree.br c h >>= k = .br c fun x => h x >>= k := by
  rw [bind_def]; simp
@[simp] theorem brS_bind (c : B.I) (h : B.O c → CTree E B R) (k : R → CTree E B S) :
    CTree.brS c h >>= k = .brS c fun x => h x >>= k := by
  simp [brS_eq]

instance : LawfulMonad (CTree E B) := LawfulMonad.mk' (CTree E B)
  (id_map := by
    intro _ t
    show t >>= (fun x => pure x) = t
    ext n
    induction n generalizing t; congr 0
    cases t <;> simp [*])
  (pure_bind := fun _ _ => pure_bind' _ _)
  (bind_assoc := by
    intro _ _ _ t1 t2 t3
    ext n
    induction n generalizing t1; congr 0
    cases t1 <;> simp [*])

instance : MonoBind (CTree E B) where
  bind_mono_left := by
    intro _ _ _ _ _ _
    apply bind_mono (fun x => x) <;> grind [monotone]
  bind_mono_right := by
    intro _ _ a _ _ _
    apply bind_mono (fun _ => a) (fun x => x)
    · grind [monotone]
    · grind [monotone]
    · intro _; grind

@[simp] theorem map_stuck (f : R → S) : f <$> (CTree.stuck : CTree E B R) = .stuck := by
  simp [← bind_pure_comp]
@[simp] theorem map_step (f : R → S) (t : CTree E B R) : f <$> t.step = (f <$> t).step := by
  simp [← bind_pure_comp]
@[simp] theorem map_guard (f : R → S) (t : CTree E B R) : f <$> t.guard = (f <$> t).guard := by
  simp [← bind_pure_comp]
@[simp] theorem map_vis (f : R → S) (e : E.I) (k : E.O e → CTree E B R) :
    f <$> CTree.vis e k = .vis e fun x => f <$> k x := by
  simp [← bind_pure_comp]
@[simp] theorem map_br (f : R → S) (c : B.I) (k : B.O c → CTree E B R) :
    f <$> CTree.br c k = .br c fun x => f <$> k x := by
  simp [← bind_pure_comp]
@[simp] theorem map_brS (f : R → S) (c : B.I) (k : B.O c → CTree E B R) :
    f <$> CTree.brS c k = .brS c fun x => f <$> k x := by
  simp [← bind_pure_comp]


@[simp] theorem spin_bind (k : R → CTree E B S) : (CTree.spin : CTree E B R) >>= k = .spin :=
  spin_bind' k

/-! ## Injected events and branchings, atomic trees -/

/-- `brS` is monotone in its continuation. -/
@[partial_fixpoint_monotone]
theorem brS_mono α [PartialOrder α] c (f : α → B.O c → CTree E B R) :
    monotone f → monotone (fun x => CTree.brS c (f x)) := by
  intro hf
  apply br_mono α c (fun a o => CTree.step (f a o))
  intro a b h o
  exact step_mono α (fun a => f a o) (fun a b h => hf a b h o) a b h

/-- An event of a sub-interface `E₁ -< E`. -/
def CTree.vis' {E₁ : Effect.{u}} [E₁ -< E] (e : E₁.I) (k : E₁.O e → CTree E B R) :
    CTree E B R :=
  .vis (Subeffect.map e).1 fun x => k ((Subeffect.map e).2 x)

/-- A branching over a sub-interface `B₁ -< B`. -/
def CTree.br' {B₁ : Effect.{u}} [B₁ -< B] (c : B₁.I) (k : B₁.O c → CTree E B R) :
    CTree E B R :=
  .br (Subeffect.map c).1 fun x => k ((Subeffect.map c).2 x)

/-- A branching over a sub-interface `B₁ -< B` whose branches first take a step. -/
def CTree.brS' {B₁ : Effect.{u}} [B₁ -< B] (c : B₁.I) (k : B₁.O c → CTree E B R) :
    CTree E B R :=
  .br' c fun x => .step (k x)

/-- A subeffect embedding whose answer conversion is surjective, as for Rocq's `-<` (which
preserves answer types): every answer of the sub-interface is reachable. Needed to show that every
branch of an injected branching (`br'`, `br2`, …) is taken. -/
class LawfulSubeffect (E₁ E₂ : Effect.{u}) [E₁ -< E₂] : Prop where
  map_surj : ∀ (i : E₁.I) (x : E₁.O i), ∃ y, (Subeffect.map (E₂ := E₂) i).2 y = x

instance {E₁ : Effect.{u}} : LawfulSubeffect E₁ E₁ := ⟨fun _ x => ⟨x, rfl⟩⟩

instance {E₁ E₂ E' : Effect.{u}} [E₁ -< E'] [E₂ -< E'] [h₁ : LawfulSubeffect E₁ E']
    [h₂ : LawfulSubeffect E₂ E'] : LawfulSubeffect (E₁ ⊕ₑ E₂) E' where
  map_surj
    | .inl i, x => h₁.map_surj i x
    | .inr i, x => h₂.map_surj i x

instance (priority := mid) {E₁ E₂ E' : Effect.{u}} [E₁ -< E₂] [h : LawfulSubeffect E₁ E₂] :
    LawfulSubeffect E₁ (E₂ ⊕ₑ E') where
  map_surj i x := h.map_surj i x

instance (priority := low) {E₁ E₂ E' : Effect.{u}} [E₁ -< E₂] [h : LawfulSubeffect E₁ E₂] :
    LawfulSubeffect E₁ (E' ⊕ₑ E₂) where
  map_surj i x := h.map_surj i x

@[partial_fixpoint_monotone]
theorem vis'_mono α [PartialOrder α] {E₁ : Effect.{u}} [E₁ -< E] e
    (f : α → E₁.O e → CTree E B R) : monotone f → monotone (fun x => CTree.vis' e (f x)) := by
  intro hf
  exact vis_mono α _ (fun a x => f a ((Subeffect.map e).2 x)) fun a b h x => hf a b h _

@[partial_fixpoint_monotone]
theorem br'_mono α [PartialOrder α] {B₁ : Effect.{u}} [B₁ -< B] c
    (f : α → B₁.O c → CTree E B R) : monotone f → monotone (fun x => CTree.br' c (f x)) := by
  intro hf
  exact br_mono α _ (fun a x => f a ((Subeffect.map c).2 x)) fun a b h x => hf a b h _

@[partial_fixpoint_monotone]
theorem brS'_mono α [PartialOrder α] {B₁ : Effect.{u}} [B₁ -< B] c
    (f : α → B₁.O c → CTree E B R) : monotone f → monotone (fun x => CTree.brS' c (f x)) := by
  intro hf
  apply br'_mono α c (fun a o => CTree.step (f a o))
  intro a b h o
  exact step_mono α (fun a => f a o) (fun a b h => hf a b h o) a b h

/-- Atomic tree triggering a single event. -/
def CTree.trigger (e : E.I) : CTree E B (E.O e) := .vis e pure
/-- Atomic tree triggering a single event of a sub-interface. -/
def CTree.trigger' (E₁ : Effect.{u}) [E₁ -< E] (e : E₁.I) : CTree E B (E₁.O e) := .vis' e pure
/-- Atomic tree with a single branching. -/
def CTree.branch (c : B.I) : CTree E B (B.O c) := .br c pure
/-- Atomic tree with a single branching over a sub-interface. -/
def CTree.branch' (B₁ : Effect.{u}) [B₁ -< B] (c : B₁.I) : CTree E B (B₁.O c) := .br' c pure
/-- Atomic tree with a single branching whose branches first take a step. -/
def CTree.branchS (c : B.I) : CTree E B (B.O c) := .brS c pure
/-- `branchS` over a sub-interface. -/
def CTree.branchS' (B₁ : Effect.{u}) [B₁ -< B] (c : B₁.I) : CTree E B (B₁.O c) := .brS' c pure
/-- Ignore the result of a tree. -/
def CTree.ignore (t : CTree E B R) : CTree E B PUnit := (fun _ => ⟨⟩) <$> t

@[simp] theorem vis'_bind {E₁ : Effect.{u}} [E₁ -< E] (e : E₁.I) (h : E₁.O e → CTree E B R)
    (k : R → CTree E B S) : CTree.vis' e h >>= k = .vis' e fun x => h x >>= k := by
  simp [CTree.vis']
@[simp] theorem br'_bind {B₁ : Effect.{u}} [B₁ -< B] (c : B₁.I) (h : B₁.O c → CTree E B R)
    (k : R → CTree E B S) : CTree.br' c h >>= k = .br' c fun x => h x >>= k := by
  simp [CTree.br']
@[simp] theorem brS'_bind {B₁ : Effect.{u}} [B₁ -< B] (c : B₁.I) (h : B₁.O c → CTree E B R)
    (k : R → CTree E B S) : CTree.brS' c h >>= k = .brS' c fun x => h x >>= k := by
  simp [CTree.brS']

/-! ## Bounded branching -/

section Branching
variable (t u v w : CTree E B R)

def CTree.br2 [B2 -< B] : CTree E B R :=
  .br' (B₁ := B2) ⟨⟩ fun b : ULift Bool => if b.down then t else u
def CTree.brS2 [B2 -< B] : CTree E B R :=
  .brS' (B₁ := B2) ⟨⟩ fun b : ULift Bool => if b.down then t else u
def CTree.br3 [B3 -< B] : CTree E B R :=
  .br' (B₁ := B3) ⟨⟩ fun n : ULift (Fin 3) => match n.down.val with | 0 => t | 1 => u | _ => v
def CTree.brS3 [B3 -< B] : CTree E B R :=
  .brS' (B₁ := B3) ⟨⟩ fun n : ULift (Fin 3) => match n.down.val with | 0 => t | 1 => u | _ => v
def CTree.br4 [B4 -< B] : CTree E B R :=
  .br' (B₁ := B4) ⟨⟩ fun n : ULift (Fin 4) =>
    match n.down.val with | 0 => t | 1 => u | 2 => v | _ => w
def CTree.brS4 [B4 -< B] : CTree E B R :=
  .brS' (B₁ := B4) ⟨⟩ fun n : ULift (Fin 4) =>
    match n.down.val with | 0 => t | 1 => u | 2 => v | _ => w
/-- Finite branching over `n` branches. -/
def CTree.brn [Bn -< B] (n : Nat) (k : Fin n → CTree E B R) : CTree E B R :=
  .br' (B₁ := Bn) ⟨n⟩ fun x : ULift (Fin n) => k x.down
def CTree.brSn [Bn -< B] (n : Nat) (k : Fin n → CTree E B R) : CTree E B R :=
  .brS' (B₁ := Bn) ⟨n⟩ fun x : ULift (Fin n) => k x.down
/-- Countable branching. -/
def CTree.brN [BN -< B] (k : Nat → CTree E B R) : CTree E B R :=
  .br' (B₁ := BN) ⟨⟩ fun x : ULift Nat => k x.down
def CTree.brSN [BN -< B] (k : Nat → CTree E B R) : CTree E B R :=
  .brS' (B₁ := BN) ⟨⟩ fun x : ULift Nat => k x.down

end Branching

/-! ## Loops -/

/-- Observable divergence: `step` forever. -/
def CTree.spinS : CTree E B R := spinS.step
partial_fixpoint

/-- Divergence by branching forever over `c`. -/
def CTree.spin_gen (c : B.I) : CTree E B R := .br c fun _ => spin_gen c
partial_fixpoint

/-- Observable divergence by branching forever over `c`. -/
def CTree.spinS_gen (c : B.I) : CTree E B R := .brS c fun _ => spinS_gen c
partial_fixpoint

/-- Repeat a computation forever, guarding each iteration. -/
def CTree.forever (k : R → CTree E B R) (i : R) : CTree E B R :=
  k i >>= fun i => .guard (forever k i)
partial_fixpoint

/-- Guarded iteration: `inl` continues the loop (under a `guard`), `inr` returns. -/
def CTree.iter {I : Type u} (step : I → CTree E B (I ⊕ R)) (i : I) : CTree E B R :=
  step i >>= fun | .inl l => .guard (iter step l) | .inr r => pure r
partial_fixpoint

theorem unfold_spinS : (CTree.spinS : CTree E B R) = .step .spinS := by
  rw (occs := .pos [1]) [CTree.spinS]
theorem unfold_spin_gen (c : B.I) : (CTree.spin_gen c : CTree E B R) = .br c fun _ => .spin_gen c := by
  rw (occs := .pos [1]) [CTree.spin_gen]
theorem unfold_spinS_gen (c : B.I) :
    (CTree.spinS_gen c : CTree E B R) = .brS c fun _ => .spinS_gen c := by
  rw (occs := .pos [1]) [CTree.spinS_gen]
theorem unfold_forever (k : R → CTree E B R) (i : R) :
    CTree.forever k i = k i >>= fun i => .guard (.forever k i) := by
  rw (occs := .pos [1]) [CTree.forever]
theorem unfold_iter {I : Type u} (step : I → CTree E B (I ⊕ R)) (i : I) :
    CTree.iter step i = step i >>= fun | .inl l => .guard (.iter step l) | .inr r => pure r := by
  rw (occs := .pos [1]) [CTree.iter]

@[simp] theorem spinS_unfold : (CTree.spinS : CTree E B R).unfold = .step .spinS := by
  rw (occs := .pos [1]) [unfold_spinS]; simp

@[simp] theorem spin_gen_unfold (c : B.I) :
    (CTree.spin_gen c : CTree E B R).unfold = .br c fun _ => .spin_gen c := by
  rw (occs := .pos [1]) [unfold_spin_gen]; simp

@[simp] theorem spinS_bind (k : R → CTree E B S) : (CTree.spinS : CTree E B R) >>= k = .spinS := by
  ext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bind_def, spinS_unfold]
    conv => rhs; rw [unfold_spinS]
    simp [ih]

/-! ## Instances -/

instance : ITree.MonadIter (CTree E B) := ⟨fun f i => CTree.iter f i⟩

@[simp] theorem iter_eq {α β : Type u} :
    @ITree.MonadIter.iter (CTree E B) _ α β = CTree.iter := rfl

instance {E₁ : Effect.{u}} [E₁ -< E] : MonadTrigger E₁ (CTree E B) := ⟨CTree.trigger' E₁⟩
instance {B₁ : Effect.{u}} [B₁ -< B] : MonadBr B₁ (CTree E B) := ⟨CTree.branch' B₁⟩
instance : MonadStuck (CTree E B) := ⟨.stuck⟩
instance : MonadStep (CTree E B) := ⟨.step (pure ⟨⟩)⟩

end CTree
